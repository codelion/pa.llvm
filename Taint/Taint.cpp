//===- Taint.cpp - Taint Analysis based Optimization for Symbolic Execution -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements taint analysis based optimization which helps in symbolic execution
//  of the program (path feasibility queries).
//
// Specifically, this:
//   * Assumes values are untainted unless proven otherwise
//   * Assumes BasicBlocks are untainted unless proven otherwise
//   * Assumes user input values to be tainted, and propagates them
//   * Removes all untainted and unreachable instructions
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "taint"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PointerIntPair.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <map>
using namespace llvm;

STATISTIC(NumInstRemoved, "Number of instructions removed");
STATISTIC(NumDeadBlocks , "Number of basic blocks unreachable");

STATISTIC(IPNumInstRemoved, "Number of instructions removed by IPTaint");
STATISTIC(IPNumArgsTainted ,"Number of tainted arguments propagated by IPTaint");
STATISTIC(IPNumGlobalTaint, "Number of globals found to be tainted by IPTaint");

namespace {
/// LatticeVal class - This class represents the different lattice values that
/// an LLVM value may occupy.  It is a simple class with value semantics.
///
class LatticeVal {
  enum LatticeValueTy {
    /// taint_may - This LLVM Value may be tainted.
    taint_may,
    
    /// taint_must - This LLVM Value is definately tainted.
    taint_must,

    /// taint_not - This LLVM Value is untainted.
    taint_not,
    
    /// taint_bot - This instruction is not reachable
    taint_bot
  };

  /// Val: This stores the current lattice value 
  LatticeValueTy Val;
  
  LatticeValueTy getLatticeValue() const {
    return Val;
  }
  
public:
  LatticeVal() : Val(taint_not) {}
  
  bool isUntainted() const { return getLatticeValue() == taint_not; }
  bool isTainted() const {
    return getLatticeValue() == taint_must || getLatticeValue() == taint_may;
  }
  bool isBottom() const { return getLatticeValue() == taint_bot; }

  /// markBottom - Return true if this is a change in status.
  bool markBottom() {
    if (isBottom())
      return false;
    
    Val = taint_bot;
    return true;
  }

  /// markTainted - Return true if this is a change in status.
  bool markTainted() {
    if (getLatticeValue() == taint_must) { // taint_must but not taint_may
      return false;
    }
    
    if (isUntainted()) {
      Val = taint_must;
    } else {
      assert(getLatticeValue() == taint_bot && 
             "Cannot move from taint_bot to taint_must!");
      Val = taint_must; //taint_may to taint_must
    }
    return true;
  }

  /// markUntainted - Return true if this is a change in status.
  bool markUntainted() {
    if (getLatticeValue() == taint_not) { // taint_not
      return false;
    }
    
    if (isTainted()) {
      Val = taint_not;
    } else {
      assert(getLatticeValue() == taint_bot && 
             "Cannot move from taint_bot to taint_not!");
      //Val = taint_must; //taint_ to taint_must
    }
    return true;
  }
  /// markMaybetainted - Return true if this is a change in status.
  bool markMaybetainted() {
    if (isTainted()) { //already tainted
      return false;
    }
    if (isUntainted()) {
      Val = taint_may;
    } else {
      assert(getLatticeValue() == taint_bot && 
             "Cannot move from taint_bot to taint_may!");
    }
    return true;   
  }
};
} // end anonymous namespace.

namespace {

//===----------------------------------------------------------------------===//
//
/// TaintSolver - This class is a general purpose solver for Taint Propagation.
///
class TaintSolver : public InstVisitor<TaintSolver> {
  const TargetData *TD;
  SmallPtrSet<BasicBlock*, 8> BBExecutable; // The BBs that are executable.
  DenseMap<Value*, LatticeVal> ValueState;  // The state each value is in.

  /// StructValueState - This maintains ValueState for values that have
  /// StructType, for example for formal arguments, calls, insertelement, etc.
  ///
  DenseMap<std::pair<Value*, unsigned>, LatticeVal> StructValueState;
  
  /// GlobalValue - If we are tracking any values for the contents of a global
  /// variable, we keep a mapping from 
  /// the global, to the currently known value.  If the value stays
  /// taint_not, it's entry is simply removed from this map.
  DenseMap<GlobalVariable*, LatticeVal> TrackedGlobals;

  /// TrackedRetVals - If we are tracking arguments into and the return
  /// value out of a function, it will have an entry in this map, indicating
  /// what the known return value for the function is.
  DenseMap<Function*, LatticeVal> TrackedRetVals;

  /// TrackedMultipleRetVals - Same as TrackedRetVals, but used for functions
  /// that return multiple values.
  DenseMap<std::pair<Function*, unsigned>, LatticeVal> TrackedMultipleRetVals;
  
  /// MRVFunctionsTracked - Each function in TrackedMultipleRetVals is
  /// represented here for efficient lookup.
  SmallPtrSet<Function*, 16> MRVFunctionsTracked;

  /// TrackingIncomingArguments - This is the set of functions for whose
  /// arguments we make optimistic assumptions about and try to prove as
  /// taint_not.
  SmallPtrSet<Function*, 16> TrackingIncomingArguments;
  
  /// The reason for two worklists is that taint_may is the highest state
  /// on the lattice, and moving things to taint_may as fast as possible
  /// makes Taint Analysis converge much faster.
  ///
  /// By having a separate worklist, we accomplish this because everything
  /// possibly tainted will become taint_may at the soonest possible
  /// point.
  SmallVector<Value*, 64> TaintMayInstWorkList;
  SmallVector<Value*, 64> InstWorkList;


  SmallVector<BasicBlock*, 64>  BBWorkList;  // The BasicBlock work list

  /// UsersOfTaintedPHIs - Keep track of any users of PHI nodes that are not
  /// tainted, despite the fact that the PHI node is tainted.
  std::multimap<PHINode*, Instruction*> UsersOfTaintedPHIs;

  /// KnownFeasibleEdges - Entries in this set are edges which have already had
  /// PHI nodes retriggered.
  typedef std::pair<BasicBlock*, BasicBlock*> Edge;
  DenseSet<Edge> KnownFeasibleEdges;
public:
  TaintSolver(const TargetData *td) : TD(td) {}

  /// MarkBlockExecutable - This method can be used by clients to mark all of
  /// the blocks that are known to be intrinsically live in the processed unit.
  ///
  /// This returns true if the block was not considered live before.
  bool MarkBlockExecutable(BasicBlock *BB) {
    if (!BBExecutable.insert(BB)) return false;
    DEBUG(dbgs() << "Marking Block Executable: " << BB->getName() << "\n");
    BBWorkList.push_back(BB);  // Add the block to the work list!
    return true;
  }

  /// TrackValueOfGlobalVariable - Clients can use this method to
  /// inform the TaintSolver that it should track loads and stores to the
  /// specified global variable if it can.  This is only legal to call if
  /// performing Interprocedural Taint Analysis.
  void TrackValueOfGlobalVariable(GlobalVariable *GV) {
    // We only track the contents of scalar globals.
    if (GV->getType()->getElementType()->isSingleValueType()) {
      LatticeVal &IV = TrackedGlobals[GV];
      if (!isa<UndefValue>(GV->getInitializer()))
        IV.markMaybetainted();
    }
  }

  /// AddTrackedFunction - If the Taint solver is supposed to track calls into
  /// and out of the specified function (which cannot have its address taken),
  /// this method must be called.
  void AddTrackedFunction(Function *F) {
    // Add an entry, F -> undef.
    if (StructType *STy = dyn_cast<StructType>(F->getReturnType())) {
      MRVFunctionsTracked.insert(F);
      for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i)
        TrackedMultipleRetVals.insert(std::make_pair(std::make_pair(F, i),
                                                     LatticeVal()));
    } else
      TrackedRetVals.insert(std::make_pair(F, LatticeVal()));
  }

  void AddArgumentTrackedFunction(Function *F) {
    TrackingIncomingArguments.insert(F);
  }
  
  /// Solve - Solve for Taintedness and executable blocks.
  ///
  void Solve();

  /// ResolvedUndefsIn - While solving the dataflow for a function, we assume
  /// that branches on taint_bot values cannot reach any of their successors.
  /// However, this is not a safe assumption.  After we solve dataflow, this
  /// method should be use to handle this.  If this returns true, the solver
  /// should be rerun.
  bool ResolvedUndefsIn(Function &F);

  bool isBlockExecutable(BasicBlock *BB) const {
    return BBExecutable.count(BB);
  }

  LatticeVal getLatticeValueFor(Value *V) const {
    DenseMap<Value*, LatticeVal>::const_iterator I = ValueState.find(V);
    assert(I != ValueState.end() && "V is not in valuemap!");
    return I->second;
  }
  
  /*LatticeVal getStructLatticeValueFor(Value *V, unsigned i) const {
    DenseMap<std::pair<Value*, unsigned>, LatticeVal>::const_iterator I = 
      StructValueState.find(std::make_pair(V, i));
    assert(I != StructValueState.end() && "V is not in valuemap!");
    return I->second;
  }*/

  /// getTrackedRetVals - Get the inferred return value map.
  ///
  const DenseMap<Function*, LatticeVal> &getTrackedRetVals() {
    return TrackedRetVals;
  }

  /// getTrackedGlobals - Get and return the set of inferred initializers for
  /// global variables.
  const DenseMap<GlobalVariable*, LatticeVal> &getTrackedGlobals() {
    return TrackedGlobals;
  }


  void markMaybetainted(Value *V) {
    assert(!V->getType()->isStructTy() && "Should use other method");
    markMaybetainted(getValueState(V), V);
  }

  void markUntainted(Value *V) {
    assert(!V->getType()->isStructTy() && "Should use other method");
    markUntainted(getValueState(V), V);
  }
  /// markAnythingmaybetainted - Mark the specified value taint_may.  This
  /// works with both scalars and structs.
  void markAnythingmaybetainted(Value *V) {
    if (StructType *STy = dyn_cast<StructType>(V->getType()))
      for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i)
        markMaybetainted(getStructValueState(V, i), V);
    else
      markMaybetainted(getValueState(V), V);
  }

  
private:
  // markUntainted - Make a value be marked as "taint_not".  If the value
  // is not already taint_must, add it to the instruction work list so that
  // the users of the instruction are updated later.
  //
  void markUntainted(LatticeVal &IV, Value *V) {
    if (!IV.markUntainted()) return;
    DEBUG(dbgs() << "markUntainted: " <<  *V << '\n');
    if (IV.isTainted())
     TaintMayInstWorkList.push_back(V);
    else
      InstWorkList.push_back(V);
  }

   // markTainted - Make a value be marked as "taint_must".  If the value
  // is not already taint_must, add it to the instruction work list so that
  // the users of the instruction are updated later.
  //
  void markTainted(LatticeVal &IV, Value *V) {
    if (!IV.markTainted()) return;
    DEBUG(dbgs() << "markTainted: " <<  *V << '\n');
    if (IV.isTainted())
     TaintMayInstWorkList.push_back(V);
    else
      InstWorkList.push_back(V);
  }
  
  void markTainted(Value *V) {
    assert(!V->getType()->isStructTy() && "Should use other method");
    markTainted(ValueState[V], V);
  } 

  // markMaybetainted- Make a value be marked as "taint_may". If the
  // value is not already taint_may, add it to the taint_may instruction
  // work list so that the users of the instruction are updated later.
  void markMaybetainted(LatticeVal &IV, Value *V) {
    if (!IV.markMaybetainted()) return;
    
    DEBUG(dbgs() << "markMaybetainted: ";
          if (Function *F = dyn_cast<Function>(V))
            dbgs() << "Function '" << F->getName() << "'\n";
          else
            dbgs() << *V << '\n');
    // Only instructions go on the work list
    TaintMayInstWorkList.push_back(V);
  }

  void mergeInValue(LatticeVal &IV, Value *V, LatticeVal MergeWithV) {
    if (IV.isBottom() || MergeWithV.isBottom())
      return;  // Noop.
    if (IV.isTainted() && MergeWithV.isTainted())
      markTainted(IV, V);
    else if (IV.isUntainted() && MergeWithV.isTainted())
      markMaybetainted(IV, V);
  }
  
  void mergeInValue(Value *V, LatticeVal MergeWithV) {
    assert(!V->getType()->isStructTy() && "Should use other method");
    mergeInValue(ValueState[V], V, MergeWithV);
  }


  /// getValueState - Return the LatticeVal object that corresponds to the
  /// value.  This function handles the case when the value hasn't been seen yet
  /// by properly seeding constants etc.
  LatticeVal &getValueState(Value *V) {
    assert(!V->getType()->isStructTy() && "Should use getStructValueState");

    std::pair<DenseMap<Value*, LatticeVal>::iterator, bool> I =
      ValueState.insert(std::make_pair(V, LatticeVal()));
    LatticeVal &LV = I.first->second;

    if (!I.second)
      return LV;  // Common case, already in the map.

    //if (Constant *C = dyn_cast<Constant>(V)) {
      // Undef values remain undefined.
      if (!isa<UndefValue>(V))
        LV.markUntainted();          // Constants are constant
    //}
    LV.markUntainted();
    // All others are untainted by default.
    return LV;
  }

  /// getStructValueState - Return the LatticeVal object that corresponds to the
  /// value/field pair.  This function handles the case when the value hasn't
  /// been seen yet by properly seeding constants etc.
  LatticeVal &getStructValueState(Value *V, unsigned i) {
    assert(V->getType()->isStructTy() && "Should use getValueState");
    assert(i < cast<StructType>(V->getType())->getNumElements() &&
           "Invalid element #");

    std::pair<DenseMap<std::pair<Value*, unsigned>, LatticeVal>::iterator,
              bool> I = StructValueState.insert(
                        std::make_pair(std::make_pair(V, i), LatticeVal()));
    LatticeVal &LV = I.first->second;

    if (!I.second)
      return LV;  // Common case, already in the map.

    /*if (Constant *C = dyn_cast<Constant>(V)) {
      if (isa<UndefValue>(C))
        ; // Undef values remain undefined.
      else if (ConstantStruct *CS = dyn_cast<ConstantStruct>(C))
        LV.markConstant(CS->getOperand(i));      // Constants are constant.
      else if (isa<ConstantAggregateZero>(C)) {
        Type *FieldTy = cast<StructType>(V->getType())->getElementType(i);
        LV.markConstant(Constant::getNullValue(FieldTy));
      } else
        LV.markOverdefined();      // Unknown sort of constant.
    }*/
    
    // All others are untainted by default.
    return LV;
  }
 

  /// markEdgeExecutable - Mark a basic block as executable, adding it to the BB
  /// work list if it is not already executable.
  void markEdgeExecutable(BasicBlock *Source, BasicBlock *Dest) {
    if (!KnownFeasibleEdges.insert(Edge(Source, Dest)).second)
      return;  // This edge is already known to be executable!

    if (!MarkBlockExecutable(Dest)) {
      // If the destination is already executable, we just made an *edge*
      // feasible that wasn't before.  Revisit the PHI nodes in the block
      // because they have potentially new operands.
      DEBUG(dbgs() << "Marking Edge Executable: " << Source->getName()
            << " -> " << Dest->getName() << "\n");

      PHINode *PN;
      for (BasicBlock::iterator I = Dest->begin();
           (PN = dyn_cast<PHINode>(I)); ++I)
        visitPHINode(*PN);
    }
  }

  // getFeasibleSuccessors - Return a vector of booleans to indicate which
  // successors are reachable from a given terminator instruction.
  //
  void getFeasibleSuccessors(TerminatorInst &TI, SmallVector<bool, 16> &Succs);

  // isEdgeFeasible - Return true if the control flow edge from the 'From' basic
  // block to the 'To' basic block is currently feasible.
  //
  bool isEdgeFeasible(BasicBlock *From, BasicBlock *To);

  // OperandChangedState - This method is invoked on all of the users of an
  // instruction that was just changed state somehow.  Based on this
  // information, we need to update the specified user of this instruction.
  //
  void OperandChangedState(Instruction *I) {
    if (BBExecutable.count(I->getParent()))   // Inst is executable?
      visit(*I);
  }
  
  /// RemoveFromTaintedPHIs - If I has any entries in the
  /// UsersOfTaintedPHIs map for PN, remove them now.
  void RemoveFromTaintedPHIs(Instruction *I, PHINode *PN) {
    if (UsersOfTaintedPHIs.empty()) return;
    typedef std::multimap<PHINode*, Instruction*>::iterator ItTy;
    std::pair<ItTy, ItTy> Range = UsersOfTaintedPHIs.equal_range(PN);
    for (ItTy It = Range.first, E = Range.second; It != E;) {
      if (It->second == I)
        UsersOfTaintedPHIs.erase(It++);
      else
        ++It;
    }
  }

  /// InsertInTaintedPHIs - Insert an entry in the UsersOfTaintedPHIs
  /// map for I and PN, but if one is there already, do not create another.
  /// (Duplicate entries do not break anything directly, but can lead to
  /// exponential growth of the table in rare cases.)
  void InsertInTaintedPHIs(Instruction *I, PHINode *PN) {
    typedef std::multimap<PHINode*, Instruction*>::iterator ItTy;
    std::pair<ItTy, ItTy> Range = UsersOfTaintedPHIs.equal_range(PN);
    for (ItTy J = Range.first, E = Range.second; J != E; ++J)
      if (J->second == I)
        return;
    UsersOfTaintedPHIs.insert(std::make_pair(PN, I));
  }

private:
  friend class InstVisitor<TaintSolver>;

  // visit implementations - Something changed in this instruction.  Either an
  // operand made a transition, or the instruction is newly executable.  Change
  // the value type of I to reflect these changes if appropriate.
  void visitPHINode(PHINode &I);

  // Terminators
  void visitReturnInst(ReturnInst &I);
  void visitTerminatorInst(TerminatorInst &TI);

  void visitCastInst(CastInst &I);
  void visitSelectInst(SelectInst &I);
  void visitBinaryOperator(Instruction &I);
  void visitCmpInst(CmpInst &I);
  void visitExtractElementInst(ExtractElementInst &I);
  void visitInsertElementInst(InsertElementInst &I);
  void visitShuffleVectorInst(ShuffleVectorInst &I);
  void visitExtractValueInst(ExtractValueInst &EVI);
  void visitInsertValueInst(InsertValueInst &IVI);
  void visitLandingPadInst(LandingPadInst &I) { markAnythingmaybetainted(&I); }

  // Instructions that cannot be folded away.
  void visitStoreInst     (StoreInst &I);
  void visitLoadInst      (LoadInst &I);
  void visitGetElementPtrInst(GetElementPtrInst &I);
  void visitCallInst      (CallInst &I) {
    visitCallSite(&I);
  }
  void visitInvokeInst    (InvokeInst &II) {
    visitCallSite(&II);
    visitTerminatorInst(II);
  }
  void visitCallSite      (CallSite CS);

  void visitResumeInst    (TerminatorInst &I) { /*returns void*/ }
  void visitUnwindInst    (TerminatorInst &I) { /*returns void*/ }
  void visitUnreachableInst(TerminatorInst &I) { /*returns void*/ }
  void visitFenceInst     (FenceInst &I) { /*returns void*/ }

  void visitAtomicCmpXchgInst (AtomicCmpXchgInst &I) { markMaybetainted(&I); }
  void visitAtomicRMWInst (AtomicRMWInst &I) { markMaybetainted(&I); }
  void visitAllocaInst    (Instruction &I) { markMaybetainted(&I); }
  void visitVAArgInst     (Instruction &I) { markAnythingmaybetainted(&I); }

  void visitInstruction(Instruction &I) {
    // If a new instruction is added to LLVM that we don't handle.
    dbgs() << "Taint: Don't know how to handle: " << I;
    markAnythingmaybetainted(&I);   // Just in case
  }

};
} // end anonymous namespace


// getFeasibleSuccessors - Return a vector of booleans to indicate which
// successors are reachable from a given terminator instruction.
//
void TaintSolver::getFeasibleSuccessors(TerminatorInst &TI,
                                       SmallVector<bool, 16> &Succs) {
  Succs.resize(TI.getNumSuccessors());
  if (BranchInst *BI = dyn_cast<BranchInst>(&TI)) {
    if (BI->isUnconditional()) {
      Succs[0] = true;
      return;
    }
    
    LatticeVal BCValue = getValueState(BI->getCondition());
    //ConstantInt *CI = BCValue.getConstantInt();
    //if (CI == 0) {
      // Overdefined condition variables, and branches on unfoldable constant
      // conditions, mean the branch could go either way.
      if (!BCValue.isBottom())
        Succs[0] = Succs[1] = true;
      return;
    }
    
    // Constant condition variables mean the branch can only go a single way.
    //Succs[CI->isZero()] = true;
    //return;
  //}
  
  if (isa<InvokeInst>(TI)) {
    // Invoke instructions successors are always executable.
    Succs[0] = Succs[1] = true;
    return;
  }
  
  if (SwitchInst *SI = dyn_cast<SwitchInst>(&TI)) {
    if (TI.getNumSuccessors() < 2) {
      Succs[0] = true;
      return;
    }
    LatticeVal SCValue = getValueState(SI->getCondition());
    //ConstantInt *CI = SCValue.getConstantInt();
    
    //if (CI == 0) {   // Overdefined or undefined condition?
      // All destinations are executable!
      if (!SCValue.isBottom())
        Succs.assign(TI.getNumSuccessors(), true);
      return;
    //}
      
    //Succs[SI->findCaseValue(CI)] = true;
   // return;
  }
  
  // TODO: This could be improved if the operand is a [cast of a] BlockAddress.
  if (isa<IndirectBrInst>(&TI)) {
    // Just mark all destinations executable!
    Succs.assign(TI.getNumSuccessors(), true);
    return;
  }
  
#ifndef NDEBUG
  dbgs() << "Unknown terminator instruction: " << TI << '\n';
#endif
  llvm_unreachable("Taint: Don't know how to handle this terminator!");
}


// isEdgeFeasible - Return true if the control flow edge from the 'From' basic
// block to the 'To' basic block is currently feasible.
//
bool TaintSolver::isEdgeFeasible(BasicBlock *From, BasicBlock *To) {
  assert(BBExecutable.count(To) && "Dest should always be alive!");

  // Make sure the source basic block is executable!!
  if (!BBExecutable.count(From)) return false;

  // Check to make sure this edge itself is actually feasible now.
  TerminatorInst *TI = From->getTerminator();
  if (BranchInst *BI = dyn_cast<BranchInst>(TI)) {
    if (BI->isUnconditional())
      return true;
    
    LatticeVal BCValue = getValueState(BI->getCondition());

    // Overdefined condition variables mean the branch could go either way,
    // undef conditions mean that neither edge is feasible yet.
    //ConstantInt *CI = BCValue.getConstantInt();
    //if (CI == 0)
      return !BCValue.isBottom();
    
    // Constant condition variables mean the branch can only go a single way.
    // return BI->getSuccessor(CI->isZero()) == To;
  }
  
  // Invoke instructions successors are always executable.
  if (isa<InvokeInst>(TI))
    return true;
  
  if (SwitchInst *SI = dyn_cast<SwitchInst>(TI)) {
    if (SI->getNumSuccessors() < 2)
      return true;

    LatticeVal SCValue = getValueState(SI->getCondition());
    //ConstantInt *CI = SCValue.getConstantInt();
    
    //if (CI == 0)
      return !SCValue.isBottom();

    // Make sure to skip the "default value" which isn't a value
    //for (unsigned i = 1, E = SI->getNumSuccessors(); i != E; ++i)
    //  if (SI->getSuccessorValue(i) == CI) // Found the taken branch.
    //    return SI->getSuccessor(i) == To;

    // If the constant value is not equal to any of the branches, we must
    // execute default branch.
    //return SI->getDefaultDest() == To;
  }
  
  // Just mark all destinations executable!
  // TODO: This could be improved if the operand is a [cast of a] BlockAddress.
  if (isa<IndirectBrInst>(TI))
    return true;
  
#ifndef NDEBUG
  dbgs() << "Unknown terminator instruction: " << *TI << '\n';
#endif
  llvm_unreachable(0);
}

// visit Implementations - Something changed in this instruction, either an
// operand made a transition, or the instruction is newly executable.  Change
// the value type of I to reflect these changes if appropriate.  This method
// makes sure to do the following actions:
//
// 1. If a phi node merges two values in, and has conflicting value coming
//    from different branches (taint_not and taint_must), or if the PHI node merges in an taint_may
//    value, then the PHI node becomes taint_may.
// 2. If a phi node merges only taint_not in, the
//    PHI node becomes taint_not
// 3. If V <- x (op) y && isUntainted(x) && isUntainted(y) V = taint_not
// 4. If V <- x (op) y && (isTainted(x) || isTainted(y)) V = taint_may
// 5. If V <- MEM or V <- CALL or V <- (unknown) then V = taint_may
// 6. If a conditional branch has a value that is not bottom, make the selected
//    destination executable
// 7. If a conditional branch has a value that is not bottom, make all
//    successors executable.
//
void TaintSolver::visitPHINode(PHINode &PN) {
  // If this PN returns a struct, just mark the result may be tainted.
  // TODO: We could do a lot better than this if code actually uses this.
  if (PN.getType()->isStructTy())
    return markAnythingmaybetainted(&PN);
  
  if (getValueState(&PN).isTainted()) {
    // There may be instructions using this PHI node that are not tainted
    // themselves.  If so, make sure that they know that the PHI node operand
    // changed.
    typedef std::multimap<PHINode*, Instruction*>::iterator ItTy;
    std::pair<ItTy, ItTy> Range = UsersOfTaintedPHIs.equal_range(&PN);
    
    if (Range.first == Range.second)
      return;
    
    SmallVector<Instruction*, 16> Users;
    for (ItTy I = Range.first, E = Range.second; I != E; ++I)
      Users.push_back(I->second);
    while (!Users.empty())
      visit(Users.pop_back_val());
    return;  // Quick exit
  }

  // Super-extra-high-degree PHI nodes are unlikely to ever be marked untainted,
  // and slow us down a lot.  Just mark them may be tainted.
  if (PN.getNumIncomingValues() > 64)
    return markMaybetainted(&PN);
  
  // Look at all of the executable operands of the PHI node.  If any of them
  // are tainted, the PHI becomes tainted as well.  If they are all
  // untainted, and they agree with each other, the PHI becomes 
  // untainted. 
  // If there are no executable operands, the PHI remains untainted.
  //
  //Constant *OperandVal = 0;
  for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i) {
    LatticeVal IV = getValueState(PN.getIncomingValue(i));
    if (IV.isBottom()) continue;  // Doesn't influence PHI node.

    if (!isEdgeFeasible(PN.getIncomingBlock(i), PN.getParent()))
      continue;
    
    if (IV.isTainted())    // PHI node becomes overdefined!
      return markMaybetainted(&PN);

    //if (OperandVal == 0) {   // Grab the first value.
     // OperandVal = IV.getConstant();
     // continue;
    //}
    
    // There is already a reachable operand.  If we conflict with it,
    // then the PHI node becomes overdefined.  If we agree with it, we
    // can continue on.
    
    // Check to see if there are two different constants merging, if so, the PHI
    // node is overdefined.
    //if (IV.getConstant() != OperandVal)
    //  return markOverdefined(&PN);
  }

  // If we exited the loop, this means that the PHI node only has constant
  // arguments that agree with each other(and OperandVal is the constant) or
  // OperandVal is null because there are no defined incoming arguments.  If
  // this is the case, the PHI remains undefined.
  //
  //if (OperandVal)
    markUntainted(&PN);      // Acquire operand value
}




void TaintSolver::visitReturnInst(ReturnInst &I) {
  if (I.getNumOperands() == 0) return;  // ret void

  Function *F = I.getParent()->getParent();
  Value *ResultOp = I.getOperand(0);
  
  // If we are tracking the return value of this function, merge it in.
  if (!TrackedRetVals.empty() && !ResultOp->getType()->isStructTy()) {
    DenseMap<Function*, LatticeVal>::iterator TFRVI =
      TrackedRetVals.find(F);
    if (TFRVI != TrackedRetVals.end()) {
      mergeInValue(TFRVI->second, F, getValueState(ResultOp));
      return;
    }
  }
  
  // Handle functions that return multiple values.
  if (!TrackedMultipleRetVals.empty()) {
    if (StructType *STy = dyn_cast<StructType>(ResultOp->getType()))
      if (MRVFunctionsTracked.count(F))
        for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i)
          mergeInValue(TrackedMultipleRetVals[std::make_pair(F, i)], F,
                       getStructValueState(ResultOp, i));
    
  }
}

void TaintSolver::visitTerminatorInst(TerminatorInst &TI) {
  SmallVector<bool, 16> SuccFeasible;
  getFeasibleSuccessors(TI, SuccFeasible);

  BasicBlock *BB = TI.getParent();

  // Mark all feasible successors executable.
  for (unsigned i = 0, e = SuccFeasible.size(); i != e; ++i)
    if (SuccFeasible[i])
      markEdgeExecutable(BB, TI.getSuccessor(i));
}

void TaintSolver::visitCastInst(CastInst &I) {
  LatticeVal OpSt = getValueState(I.getOperand(0));
  if (OpSt.isTainted())          // Inherit overdefinedness of operand
    markMaybetainted(&I);
  //else if (OpSt.isUntained())        // Propagate constant value
  //  markConstant(&I, ConstantExpr::getCast(I.getOpcode(), 
  //                                         OpSt.getConstant(), I.getType()));
}


void TaintSolver::visitExtractValueInst(ExtractValueInst &EVI) {
  // If this returns a struct, mark all elements over defined, we don't track
  // structs in structs.
  if (EVI.getType()->isStructTy())
    return markAnythingmaybetainted(&EVI);
    
  // If this is extracting from more than one level of struct, we don't know.
  if (EVI.getNumIndices() != 1)
    return markMaybetainted(&EVI);

  Value *AggVal = EVI.getAggregateOperand();
  if (AggVal->getType()->isStructTy()) {
    unsigned i = *EVI.idx_begin();
    LatticeVal EltVal = getStructValueState(AggVal, i);
    mergeInValue(getValueState(&EVI), &EVI, EltVal);
  } else {
    // Otherwise, must be extracting from an array.
    return markMaybetainted(&EVI);
  }
}

void TaintSolver::visitInsertValueInst(InsertValueInst &IVI) {
  StructType *STy = dyn_cast<StructType>(IVI.getType());
  if (STy == 0)
    return markMaybetainted(&IVI);
  
  // If this has more than one index, we can't handle it, drive all results to
  // undef.
  if (IVI.getNumIndices() != 1)
    return markAnythingmaybetainted(&IVI);
  
  Value *Aggr = IVI.getAggregateOperand();
  unsigned Idx = *IVI.idx_begin();
  
  // Compute the result based on what we're inserting.
  for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
    // This passes through all values that aren't the inserted element.
    if (i != Idx) {
      LatticeVal EltVal = getStructValueState(Aggr, i);
      mergeInValue(getStructValueState(&IVI, i), &IVI, EltVal);
      continue;
    }
    
    Value *Val = IVI.getInsertedValueOperand();
    if (Val->getType()->isStructTy())
      // We don't track structs in structs.
      markMaybetainted(getStructValueState(&IVI, i), &IVI);
    else {
      LatticeVal InVal = getValueState(Val);
      mergeInValue(getStructValueState(&IVI, i), &IVI, InVal);
    }
  }
}

void TaintSolver::visitSelectInst(SelectInst &I) {
  // If this select returns a struct, just mark the result overdefined.
  // TODO: We could do a lot better than this if code actually uses this.
  if (I.getType()->isStructTy())
    return markAnythingmaybetainted(&I);
  
  LatticeVal CondValue = getValueState(I.getCondition());
  if (CondValue.isBottom())
    return;
  
  //if (ConstantInt *CondCB = CondValue.getConstantInt()) {
  //  Value *OpVal = CondCB->isZero() ? I.getFalseValue() : I.getTrueValue();
  //  mergeInValue(&I, getValueState(OpVal));
  // return;
  //}
  
  // Otherwise, the condition is overdefined or a constant we can't evaluate.
  // See if we can produce something better than overdefined based on the T/F
  // value.
  LatticeVal TVal = getValueState(I.getTrueValue());
  LatticeVal FVal = getValueState(I.getFalseValue());
  
  // select ?, C, C -> C.
  //if (TVal.isUntainted() && FVal.isUntained())
  //  return markUntainted(&I, FVal.getConstant());

  if (TVal.isBottom())   // select ?, undef, X -> X.
    return mergeInValue(&I, FVal);
  if (FVal.isBottom())   // select ?, X, undef -> X.
    return mergeInValue(&I, TVal);
  markMaybetainted(&I);
}

// Handle Binary Operators.
void TaintSolver::visitBinaryOperator(Instruction &I) {
  LatticeVal V1State = getValueState(I.getOperand(0));
  LatticeVal V2State = getValueState(I.getOperand(1));
  
  LatticeVal &IV = ValueState[&I];
  if (IV.isTainted()) return;

  //if (V1State.isConstant() && V2State.isConstant())
  //  return markConstant(IV, &I,
  //                     ConstantExpr::get(I.getOpcode(), V1State.getConstant(),
  //                                        V2State.getConstant()));
  
  // If something is undef, wait for it to resolve.
  if (!V1State.isTainted() && !V2State.isTainted())
    return;
  
  // Otherwise, one of our operands is Tainted.  Try to produce something
  // better than Tainted with some tricks.
  
  // If this is an AND or OR with 0 or -1, it doesn't matter that the other
  // operand is Tainted.
  if (I.getOpcode() == Instruction::And || I.getOpcode() == Instruction::Or) {
    LatticeVal *NonOverdefVal = 0;
    if (!V1State.isTainted())
      NonOverdefVal = &V1State;
    else if (!V2State.isTainted())
      NonOverdefVal = &V2State;

    if (NonOverdefVal) {
      if (NonOverdefVal->isBottom()) {
        // Could annihilate value.
        if (I.getOpcode() == Instruction::And)
          markUntainted(IV, &I);
        return;
      }
      
      //if (I.getOpcode() == Instruction::And) {
        // X and 0 = 0
      //  if (NonOverdefVal->getConstant()->isNullValue())
      //    return markConstant(IV, &I, NonOverdefVal->getConstant());
      //} else {
      //  if (ConstantInt *CI = NonOverdefVal->getConstantInt())
      //    if (CI->isAllOnesValue())     // X or -1 = -1
      //      return markConstant(IV, &I, NonOverdefVal->getConstant());
      //}
    }
  }


  // If both operands are PHI nodes, it is possible that this instruction has
  // a tainted value, despite the fact that the PHI node doesn't.  Check for
  // this condition now.
  if (PHINode *PN1 = dyn_cast<PHINode>(I.getOperand(0)))
    if (PHINode *PN2 = dyn_cast<PHINode>(I.getOperand(1)))
      if (PN1->getParent() == PN2->getParent()) {
        // Since the two PHI nodes are in the same basic block, they must have
        // entries for the same predecessors.  Walk the predecessor list, and
        // if all of the incoming values are constants, and the result of
        // evaluating this expression with all incoming value pairs is the
        // same, then this expression is a constant even though the PHI node
        // is not a constant!
        LatticeVal Result;
        for (unsigned i = 0, e = PN1->getNumIncomingValues(); i != e; ++i) {
          LatticeVal In1 = getValueState(PN1->getIncomingValue(i));
          BasicBlock *InBlock = PN1->getIncomingBlock(i);
          LatticeVal In2 =getValueState(PN2->getIncomingValueForBlock(InBlock));

          if (In1.isTainted() || In2.isTainted()) {
            Result.markMaybetainted();
            break;  // Cannot fold this operation over the PHI nodes!
          }
          
          //if (In1.isConstant() && In2.isConstant()) {
          //  Constant *V = ConstantExpr::get(I.getOpcode(), In1.getConstant(),
          //                                  In2.getConstant());
          //  if (Result.isBottom())
          //    Result.markUntained(V);
          //  else if (Result.isConstant() && Result.getConstant() != V) {
          //    Result.markMaybetainted();
          //    break;
          //  }
          //}
        }

        // If we found a untainted value here, then we know the instruction is
        // untainted despite the fact that the PHI nodes are tainted.
        if (Result.isUntainted()) {
          markUntainted(IV, &I);
          // Remember that this instruction is virtually using the PHI node
          // operands. 
          InsertInTaintedPHIs(&I, PN1);
          InsertInTaintedPHIs(&I, PN2);
          return;
        }
        
        if (Result.isBottom())
          return;

        // Okay, this really is overdefined now.  Since we might have
        // speculatively thought that this was not overdefined before, and
        // added ourselves to the UsersOfOverdefinedPHIs list for the PHIs,
        // make sure to clean out any entries that we put there, for
        // efficiency.
        RemoveFromTaintedPHIs(&I, PN1);
        RemoveFromTaintedPHIs(&I, PN2);
      }

  markMaybetainted(&I);
}

// Handle ICmpInst instruction.
void TaintSolver::visitCmpInst(CmpInst &I) {
  LatticeVal V1State = getValueState(I.getOperand(0));
  LatticeVal V2State = getValueState(I.getOperand(1));

  LatticeVal &IV = ValueState[&I];
  if (IV.isTainted()) return;

  if (V1State.isUntainted() && V2State.isUntainted())
    return markUntainted(IV, &I);
  
  // If operands are still undefined, wait for it to resolve.
  if (!V1State.isTainted() && !V2State.isTainted())
    return;
  
  // If something is tainted, use some tricks to avoid ending up and over
  // tainted if we can.
  
  // If both operands are PHI nodes, it is possible that this instruction has
  // a untainted value, despite the fact that the PHI node doesn't.  Check for
  // this condition now.
  if (PHINode *PN1 = dyn_cast<PHINode>(I.getOperand(0)))
    if (PHINode *PN2 = dyn_cast<PHINode>(I.getOperand(1)))
      if (PN1->getParent() == PN2->getParent()) {
        // Since the two PHI nodes are in the same basic block, they must have
        // entries for the same predecessors.  Walk the predecessor list, and
        // if all of the incoming values are constants, and the result of
        // evaluating this expression with all incoming value pairs is the
        // same, then this expression is a constant even though the PHI node
        // is not a constant!
        LatticeVal Result;
        for (unsigned i = 0, e = PN1->getNumIncomingValues(); i != e; ++i) {
          LatticeVal In1 = getValueState(PN1->getIncomingValue(i));
          BasicBlock *InBlock = PN1->getIncomingBlock(i);
          LatticeVal In2 =getValueState(PN2->getIncomingValueForBlock(InBlock));

          if (In1.isTainted() || In2.isTainted()) {
            Result.markMaybetainted();
            break;  // Cannot fold this operation over the PHI nodes!
          }
          
          if (In1.isUntainted() && In2.isUntainted()) {
            if (Result.isUntainted())
              Result.markUntainted();
            else {
              Result.markMaybetainted();
              break;
            }
          }
        }

        // If we found a Untainted value here, then we know the instruction is
        // Untainted despite the fact that the PHI nodes are tainted.
        if (Result.isUntainted()) {
          markUntainted(&I);
          // Remember that this instruction is virtually using the PHI node
          // operands.
          InsertInTaintedPHIs(&I, PN1);
          InsertInTaintedPHIs(&I, PN2);
          return;
        }
        
        if (Result.isBottom())
          return;

        // Okay, this really is tainted now.  Since we might have
        // speculatively thought that this was not tainted before, and
        // added ourselves to the UsersOfTaintedPHIs list for the PHIs,
        // make sure to clean out any entries that we put there, for
        // efficiency.
        RemoveFromTaintedPHIs(&I, PN1);
        RemoveFromTaintedPHIs(&I, PN2);
      }

  markMaybetainted(&I);
}

void TaintSolver::visitExtractElementInst(ExtractElementInst &I) {
  // TODO : Taint does not handle vectors properly.
  return markMaybetainted(&I);

#if 0
  LatticeVal &ValState = getValueState(I.getOperand(0));
  LatticeVal &IdxState = getValueState(I.getOperand(1));

  if (ValState.isOverdefined() || IdxState.isOverdefined())
    markOverdefined(&I);
  else if(ValState.isConstant() && IdxState.isConstant())
    markConstant(&I, ConstantExpr::getExtractElement(ValState.getConstant(),
                                                     IdxState.getConstant()));
#endif
}

void TaintSolver::visitInsertElementInst(InsertElementInst &I) {
  // TODO : Taint does not handle vectors properly.
  return markMaybetainted(&I);
#if 0
  LatticeVal &ValState = getValueState(I.getOperand(0));
  LatticeVal &EltState = getValueState(I.getOperand(1));
  LatticeVal &IdxState = getValueState(I.getOperand(2));

  if (ValState.isOverdefined() || EltState.isOverdefined() ||
      IdxState.isOverdefined())
    markOverdefined(&I);
  else if(ValState.isConstant() && EltState.isConstant() &&
          IdxState.isConstant())
    markConstant(&I, ConstantExpr::getInsertElement(ValState.getConstant(),
                                                    EltState.getConstant(),
                                                    IdxState.getConstant()));
  else if (ValState.isUndefined() && EltState.isConstant() &&
           IdxState.isConstant()) 
    markConstant(&I,ConstantExpr::getInsertElement(UndefValue::get(I.getType()),
                                                   EltState.getConstant(),
                                                   IdxState.getConstant()));
#endif
}

void TaintSolver::visitShuffleVectorInst(ShuffleVectorInst &I) {
  // TODO : Taint does not handle vectors properly.
  return markMaybetainted(&I);
#if 0
  LatticeVal &V1State   = getValueState(I.getOperand(0));
  LatticeVal &V2State   = getValueState(I.getOperand(1));
  LatticeVal &MaskState = getValueState(I.getOperand(2));

  if (MaskState.isUndefined() ||
      (V1State.isUndefined() && V2State.isUndefined()))
    return;  // Undefined output if mask or both inputs undefined.
  
  if (V1State.isOverdefined() || V2State.isOverdefined() ||
      MaskState.isOverdefined()) {
    markOverdefined(&I);
  } else {
    // A mix of constant/undef inputs.
    Constant *V1 = V1State.isConstant() ? 
        V1State.getConstant() : UndefValue::get(I.getType());
    Constant *V2 = V2State.isConstant() ? 
        V2State.getConstant() : UndefValue::get(I.getType());
    Constant *Mask = MaskState.isConstant() ? 
      MaskState.getConstant() : UndefValue::get(I.getOperand(2)->getType());
    markConstant(&I, ConstantExpr::getShuffleVector(V1, V2, Mask));
  }
#endif
}

// Handle getelementptr instructions.  If all operands are constants then we
// can turn this into a getelementptr ConstantExpr.
//
void TaintSolver::visitGetElementPtrInst(GetElementPtrInst &I) {
  if (ValueState[&I].isTainted()) return;

  //SmallVector<Constant*, 8> Operands;
  //Operands.reserve(I.getNumOperands());

  for (unsigned i = 0, e = I.getNumOperands(); i != e; ++i) {
    LatticeVal State = getValueState(I.getOperand(i));
    if (State.isBottom())
      return;  // Operands are not resolved yet.
    
    if (State.isTainted())
      return markMaybetainted(&I);

    //assert(State.isConstant() && "Unknown state!");
    //Operands.push_back(State.getConstant());
  }

  //Constant *Ptr = Operands[0];
  //ArrayRef<Constant *> Indices(Operands.begin() + 1, Operands.end());
  //markConstant(&I, ConstantExpr::getGetElementPtr(Ptr, Indices));
}

void TaintSolver::visitStoreInst(StoreInst &SI) {
  // If this store is of a struct, ignore it.
  if (SI.getOperand(0)->getType()->isStructTy())
    return;
  
  if (TrackedGlobals.empty() || !isa<GlobalVariable>(SI.getOperand(1)))
    return;
  
  GlobalVariable *GV = cast<GlobalVariable>(SI.getOperand(1));
  DenseMap<GlobalVariable*, LatticeVal>::iterator I = TrackedGlobals.find(GV);
  if (I == TrackedGlobals.end() || I->second.isTainted()) return;

  // Get the value we are storing into the global, then merge it.
  mergeInValue(I->second, GV, getValueState(SI.getOperand(0)));
  if (I->second.isTainted())
    TrackedGlobals.erase(I);      // No need to keep tracking this!
}


// Handle load instructions.  If the operand is a constant pointer to a constant
// global, we can replace the load with the loaded constant value!
void TaintSolver::visitLoadInst(LoadInst &I) {
  // If this load is of a struct, just mark the result overdefined.
  if (I.getType()->isStructTy())
    return markAnythingmaybetainted(&I);
  
  LatticeVal PtrVal = getValueState(I.getOperand(0));
  if (PtrVal.isBottom()) return;   // The pointer is not resolved yet!
  
  LatticeVal &IV = ValueState[&I];
  if (IV.isTainted()) return;

  if (!PtrVal.isUntainted() || I.isVolatile())
    return markMaybetainted(IV, &I);
    
  //Constant *Ptr = PtrVal.getConstant();

  // load null -> null
  //if (isa<ConstantPointerNull>(Ptr) && I.getPointerAddressSpace() == 0)
  //  return markConstant(IV, &I, Constant::getNullValue(I.getType()));
  
  // Transform load (constant global) into the value loaded.
  //if (GlobalVariable *GV = dyn_cast<GlobalVariable>(Ptr)) {
  //  if (!TrackedGlobals.empty()) {
      // If we are tracking this global, merge in the known value for it.
  //    DenseMap<GlobalVariable*, LatticeVal>::iterator It =
  //      TrackedGlobals.find(GV);
  //    if (It != TrackedGlobals.end()) {
  //      mergeInValue(IV, &I, It->second);
  //      return;
  //    }
  //  }
  //}

  // Transform load from a constant into a constant if possible.
  //if (Constant *C = ConstantFoldLoadFromConstPtr(Ptr, TD))
  //  return markConstant(IV, &I, C);

  // Otherwise we cannot say for certain what value this load will produce.
  // Bail out.
  markMaybetainted(IV, &I);
}

void TaintSolver::visitCallSite(CallSite CS) {
  Function *F = CS.getCalledFunction();
  Instruction *I = CS.getInstruction();
  
  // The common case is that we aren't tracking the callee, either because we
  // are not doing interprocedural analysis or the callee is indirect, or is
  // external.  Handle these cases first.
  if (F == 0 || F->isDeclaration()) {
CallOverdefined:
    // Void return and not tracking callee, just bail.
    if (I->getType()->isVoidTy()) return;
    
    // Otherwise, if we have a single return value case, and if the function is
    // a declaration, maybe we can constant fold it.
    if (F && F->isDeclaration() && !I->getType()->isStructTy() &&
        canConstantFoldCallTo(F)) {
      
      SmallVector<Constant*, 8> Operands;
      for (CallSite::arg_iterator AI = CS.arg_begin(), E = CS.arg_end();
           AI != E; ++AI) {
        LatticeVal State = getValueState(*AI);
        
        if (State.isBottom())
          return;  // Operands are not resolved yet.
        if (State.isTainted())
          return markMaybetainted(I);
        assert(State.isUntainted() && "Unknown state!");
        //Operands.push_back(State.getConstant());
      }
     
      // If we can constant fold this, mark the result of the call as a
      // constant.
      //if (ConstantFoldCall(F, Operands))
      // return markUntainted(I);
    }

    // Otherwise, we don't know anything about this call, mark it overdefined.
    return markAnythingmaybetainted(I);
  }

  // If this is a local function that doesn't have its address taken, mark its
  // entry block executable and merge in the actual arguments to the call into
  // the formal arguments of the function.
  if (!TrackingIncomingArguments.empty() && TrackingIncomingArguments.count(F)){
    MarkBlockExecutable(F->begin());
    
    // Propagate information from this call site into the callee.
    CallSite::arg_iterator CAI = CS.arg_begin();
    for (Function::arg_iterator AI = F->arg_begin(), E = F->arg_end();
         AI != E; ++AI, ++CAI) {
      // If this argument is byval, and if the function is not readonly, there
      // will be an implicit copy formed of the input aggregate.
      if (AI->hasByValAttr() && !F->onlyReadsMemory()) {
        markMaybetainted(AI);
        continue;
      }
      
      if (StructType *STy = dyn_cast<StructType>(AI->getType())) {
        for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
          LatticeVal CallArg = getStructValueState(*CAI, i);
          mergeInValue(getStructValueState(AI, i), AI, CallArg);
        }
      } else {
        mergeInValue(AI, getValueState(*CAI));
      }
    }
  }
  
  // If this is a single/zero retval case, see if we're tracking the function.
  if (StructType *STy = dyn_cast<StructType>(F->getReturnType())) {
    if (!MRVFunctionsTracked.count(F))
      goto CallOverdefined;  // Not tracking this callee.
    
    // If we are tracking this callee, propagate the result of the function
    // into this call site.
    for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i)
      mergeInValue(getStructValueState(I, i), I, 
                   TrackedMultipleRetVals[std::make_pair(F, i)]);
  } else {
    DenseMap<Function*, LatticeVal>::iterator TFRVI = TrackedRetVals.find(F);
    if (TFRVI == TrackedRetVals.end())
      goto CallOverdefined;  // Not tracking this callee.
      
    // If so, propagate the return value of the callee into this call result.
    mergeInValue(I, TFRVI->second);
  }
}

void TaintSolver::Solve() {
  // Process the work lists until they are empty!
  while (!BBWorkList.empty() || !InstWorkList.empty() ||
         !TaintMayInstWorkList.empty()) {
    // Process the taint_may instruction's work list first, which drives other
    // things to taint_may more quickly.
    while (!TaintMayInstWorkList.empty()) {
      Value *I = TaintMayInstWorkList.pop_back_val();

      DEBUG(dbgs() << "\nPopped off OI-WL: " << *I << '\n');

      // "I" got into the work list because it either made the transition from
      // bottom to Untainted
      //
      // Anything on this worklist that is tainted need not be visited
      // since all of its users will have already been marked as tainted
      // Update all of the users of this instruction's value.
      //
      for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
           UI != E; ++UI)
        if (Instruction *I = dyn_cast<Instruction>(*UI))
          OperandChangedState(I);
    }
    
    // Process the instruction work list.
    while (!InstWorkList.empty()) {
      Value *I = InstWorkList.pop_back_val();

      DEBUG(dbgs() << "\nPopped off I-WL: " << *I << '\n');

      // "I" got into the work list because it made the transition from tainted to
      // untainted.
      //
      // Anything on this worklist that is tanited need not be visited
      // since all of its users will have already been marked as tanited.
      // Update all of the users of this instruction's value.
      //
      if (I->getType()->isStructTy() || !getValueState(I).isTainted())
        for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
             UI != E; ++UI)
          if (Instruction *I = dyn_cast<Instruction>(*UI))
            OperandChangedState(I);
    }

    // Process the basic block work list.
    while (!BBWorkList.empty()) {
      BasicBlock *BB = BBWorkList.back();
      BBWorkList.pop_back();

      DEBUG(dbgs() << "\nPopped off BBWL: " << *BB << '\n');

      // Notify all instructions in this basic block that they are newly
      // executable.
      visit(BB);
    }
  }
}

/// ResolvedUndefsIn - While solving the dataflow for a function, we assume
/// that branches on taint_bot values cannot reach any of their successors.
/// However, this is not a safe assumption.  After we solve dataflow, this
/// method should be use to handle this.  If this returns true, the solver
/// should be rerun.
///
/// This method handles this by finding an unresolved branch and marking it one
/// of the edges from the block as being feasible, even though the condition
/// doesn't say it would otherwise be.  This allows Taint to find the rest of the
/// CFG and only slightly pessimizes the analysis results (by marking one,
/// potentially infeasible, edge feasible).  This cannot usefully modify the
/// constraints on the condition of the branch, as that would impact other users
/// of the value.
///
/// This scan also checks for values that use taint_bots, whose results are actually
/// defined.  For example, 'zext i8 undef to i32' should produce all zeros
/// conservatively, as "(zext i8 X -> i32) & 0xFF00" must always return zero,
/// even if X isn't defined.
bool TaintSolver::ResolvedUndefsIn(Function &F) {
  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    if (!BBExecutable.count(BB))
      continue;
    
    for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
      // Look for instructions which produce undef values.
      if (I->getType()->isVoidTy()) continue;
      
      if (StructType *STy = dyn_cast<StructType>(I->getType())) {
        // Only a few things that can be structs matter for undef.

        // Tracked calls must never be marked overdefined in ResolvedUndefsIn.
        if (CallSite CS = CallSite(I))
          if (Function *F = CS.getCalledFunction())
            if (MRVFunctionsTracked.count(F))
              continue;

        // extractvalue and insertvalue don't need to be marked; they are
        // tracked as precisely as their operands. 
        if (isa<ExtractValueInst>(I) || isa<InsertValueInst>(I))
          continue;

        // Send the results of everything else to tainted.  We could be
        // more precise than this but it isn't worth bothering.
        for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
          LatticeVal &LV = getStructValueState(I, i);
          if (LV.isBottom())
            markMaybetainted(LV, I);
        }
        continue;
      }

      LatticeVal &LV = getValueState(I);
      if (!LV.isBottom()) continue;

      // extractvalue is safe; check here because the argument is a struct.
      if (isa<ExtractValueInst>(I))
        continue;

      // Compute the operand LatticeVals, for convenience below.
      // Anything taking a struct is conservatively assumed to require
      // overdefined markings.
      if (I->getOperand(0)->getType()->isStructTy()) {
        markMaybetainted(I);
        return true;
      }
      LatticeVal Op0LV = getValueState(I->getOperand(0));
      LatticeVal Op1LV;
      if (I->getNumOperands() == 2) {
        if (I->getOperand(1)->getType()->isStructTy()) {
          markMaybetainted(I);
          return true;
        }

        Op1LV = getValueState(I->getOperand(1));
      }
      // If this is an instructions whose result is defined even if the input is
      // not fully defined, propagate the information.
      //Type *ITy = I->getType();
      switch (I->getOpcode()) {
      case Instruction::Add:
      case Instruction::Sub:
      case Instruction::Trunc:
      case Instruction::FPTrunc:
      case Instruction::BitCast:
        break; // Any undef -> undef
      case Instruction::FSub:
      case Instruction::FAdd:
      case Instruction::FMul:
      case Instruction::FDiv:
      case Instruction::FRem:
        // Floating-point binary operation: be conservative.
        if (Op0LV.isBottom() && Op1LV.isBottom())
          markUntainted(I);
        else
          markMaybetainted(I);
        return true;
      case Instruction::ZExt:
      case Instruction::SExt:
      case Instruction::FPToUI:
      case Instruction::FPToSI:
      case Instruction::FPExt:
      case Instruction::PtrToInt:
      case Instruction::IntToPtr:
      case Instruction::SIToFP:
      case Instruction::UIToFP:
        // undef -> 0; some outputs are impossible
        markUntainted(I);
        return true;
      case Instruction::Mul:
      case Instruction::And:
        // Both operands undef -> undef
        if (Op0LV.isBottom() && Op1LV.isBottom())
          break;
        // undef * X -> 0.   X could be zero.
        // undef & X -> 0.   X could be zero.
        markUntainted(I);
        return true;

      case Instruction::Or:
        // Both operands undef -> undef
        if (Op0LV.isBottom() && Op1LV.isBottom())
          break;
        // undef | X -> -1.   X could be -1.
        markUntainted(I);
        return true;

      case Instruction::Xor:
        // undef ^ undef -> 0; strictly speaking, this is not strictly
        // necessary, but we try to be nice to people who expect this
        // behavior in simple cases
        if (Op0LV.isBottom() && Op1LV.isBottom()) {
          markUntainted(I);
          return true;
        }
        // undef ^ X -> undef
        break;

      case Instruction::SDiv:
      case Instruction::UDiv:
      case Instruction::SRem:
      case Instruction::URem:
        // X / undef -> undef.  No change.
        // X % undef -> undef.  No change.
        if (Op1LV.isBottom()) break;
        
        // undef / X -> 0.   X could be maxint.
        // undef % X -> 0.   X could be 1.
        markUntainted(I);
        return true;
        
      case Instruction::AShr:
        // X >>a undef -> undef.
        if (Op1LV.isBottom()) break;

        // undef >>a X -> all ones
        markUntainted(I);
        return true;
      case Instruction::LShr:
      case Instruction::Shl:
        // X << undef -> undef.
        // X >> undef -> undef.
        if (Op1LV.isBottom()) break;

        // undef << X -> 0
        // undef >> X -> 0
        markUntainted(I);
        return true;
      case Instruction::Select:
        Op1LV = getValueState(I->getOperand(1));
        // undef ? X : Y  -> X or Y.  There could be commonality between X/Y.
        if (Op0LV.isBottom()) {
          if (!Op1LV.isUntainted())  // Pick the constant one if there is any.
            Op1LV = getValueState(I->getOperand(2));
        } else if (Op1LV.isBottom()) {
          // c ? undef : undef -> undef.  No change.
          Op1LV = getValueState(I->getOperand(2));
          if (Op1LV.isBottom())
            break;
          // Otherwise, c ? undef : x -> x.
        } else {
          // Leave Op1LV as Operand(1)'s LatticeValue.
        }
        
        if (Op1LV.isUntainted())
          markUntainted(I);
        else
          markMaybetainted(I);
        return true;
      case Instruction::Load:
        // A load here means one of two things: a load of undef from a global,
        // a load from an unknown pointer.  Either way, having it return undef
        // is okay.
        break;
      case Instruction::ICmp:
        // X == undef -> undef.  Other comparisons get more complicated.
        if (cast<ICmpInst>(I)->isEquality())
          break;
        markMaybetainted(I);
        return true;
      case Instruction::Call:
      case Instruction::Invoke: {
        // There are two reasons a call can have an undef result
        // 1. It could be tracked.
        // 2. It could be constant-foldable.
        // Because of the way we solve return values, tracked calls must
        // never be marked overdefined in ResolvedUndefsIn.
        if (Function *F = CallSite(I).getCalledFunction())
          if (TrackedRetVals.count(F))
            break;

        // If the call is constant-foldable, we mark it overdefined because
        // we do not know what return values are valid.
        markMaybetainted(I);
        return true;
      }
      default:
        // If we don't know what should happen here, conservatively mark it
        // overdefined.
        markMaybetainted(I);
        return true;
      }
    }
  
    // Check to see if we have a branch or switch on an undefined value.  If so
    // we force the branch to go one way or the other to make the successor
    // values live.  It doesn't really matter which way we force it.
    TerminatorInst *TI = BB->getTerminator();
    if (BranchInst *BI = dyn_cast<BranchInst>(TI)) {
      if (!BI->isConditional()) continue;
      if (!getValueState(BI->getCondition()).isBottom())
        continue;
    
      // If the input to SCCP is actually branch on undef, fix the undef to
      // false.
      if (isa<UndefValue>(BI->getCondition())) {
        BI->setCondition(ConstantInt::getFalse(BI->getContext()));
        markEdgeExecutable(BB, TI->getSuccessor(1));
        return true;
      }
      
      // Otherwise, it is a branch on a symbolic value which is currently
      // considered to be undef.  Handle this by forcing the input value to the
      // branch to false.
      markUntainted(BI->getCondition());
      return true;
    }
    
    if (SwitchInst *SI = dyn_cast<SwitchInst>(TI)) {
      if (SI->getNumSuccessors() < 2)   // no cases
        continue;
      if (!getValueState(SI->getCondition()).isBottom())
        continue;
      
      // If the input to SCCP is actually switch on undef, fix the undef to
      // the first constant.
      if (isa<UndefValue>(SI->getCondition())) {
        SI->setCondition(SI->getCaseValue(1));
        markEdgeExecutable(BB, TI->getSuccessor(1));
        return true;
      }
      
      markUntainted(SI->getCondition());
      return true;
    }
  }

  return false;

}
namespace {
  //===--------------------------------------------------------------------===//
  //
  /// Taint Class - This class uses the TaintSolver to implement a per-function
  /// Taint Propagator.
  ///
  struct Taint : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Taint() : FunctionPass(ID) {
      //initializeTaintPass(*PassRegistry::getPassRegistry());
    }

    // runOnFunction - Run the Taint Propagation
    // algorithm, and return true if the function was modified.
    //
    virtual bool runOnFunction(Function &F);
  };
} // end anonymous namespace

char Taint::ID = 0;
static RegisterPass<Taint> X("taint", "Taint Propagation", false, false);
//INITIALIZE_PASS(Taint, "taint", "Taint Propagation", false, false)

// createTaintPass - This is the public interface to this file.
//FunctionPass *llvm::createTaintPass() {
//  return new Taint();
//}

static void DeleteInstructionInBlock(BasicBlock *BB) {
  DEBUG(dbgs() << "  BasicBlock Dead:" << *BB);
  ++NumDeadBlocks;

  // Check to see if there are non-terminating instructions to delete.
  if (isa<TerminatorInst>(BB->begin()))
    return;

  // Delete the instructions backwards, as it has a reduced likelihood of having
  // to update as many def-use and use-def chains.
  Instruction *EndInst = BB->getTerminator(); // Last not to be deleted.
  while (EndInst != BB->begin()) {
    // Delete the next to last instruction.
    BasicBlock::iterator I = EndInst;
    Instruction *Inst = --I;
    //if (!Inst->use_empty())
    //  Inst->replaceAllUsesWith(UndefValue::get(Inst->getType()));
    if (isa<LandingPadInst>(Inst)) {
      EndInst = Inst;
      continue;
    }
    BB->getInstList().erase(Inst);
    ++NumInstRemoved;
  }
}

// runOnFunction() - Run the Taint Propagation algorithm,
// and return true if the function was modified.
//
bool Taint::runOnFunction(Function &F) {
  DEBUG(dbgs() << "Taint on function '" << F.getName() << "'\n");
  TaintSolver Solver(getAnalysisIfAvailable<TargetData>());

  // Mark the first block of the function as being executable.
  Solver.MarkBlockExecutable(F.begin());

  // Mark all arguments to the function as being taint_may.
  for (Function::arg_iterator AI = F.arg_begin(), E = F.arg_end(); AI != E;++AI)
    Solver.markMaybetainted(AI);

  // Solve for untainted.
  bool ResolvedUndefs = true;
  while (ResolvedUndefs) {
    Solver.Solve();
    DEBUG(dbgs() << "RESOLVING UNDEFs\n");
    ResolvedUndefs = Solver.ResolvedUndefsIn(F);
  }

  bool MadeChanges = false;

  // If we decided that there are basic blocks that are dead in this function,
  // delete their contents now.  Note that we cannot actually delete the blocks,
  // as we cannot modify the CFG of the function.

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    if (!Solver.isBlockExecutable(BB)) {
      DeleteInstructionInBlock(BB);
      MadeChanges = true;
      continue;
    }
  
    // Iterate over all of the instructions in a function, deleting those with
    // taint_not if we have found them to be of untainted values.
    //
    for (BasicBlock::iterator BI = BB->begin(), E = BB->end(); BI != E; ) {
      Instruction *Inst = BI++;
      if (Inst->getType()->isVoidTy() || isa<TerminatorInst>(Inst))
        continue;
      
      // TODO: Reconstruct structs from their elements.
      if (Inst->getType()->isStructTy())
        continue;
      
      LatticeVal IV = Solver.getLatticeValueFor(Inst);
      if (IV.isTainted())
        continue;
      
      //Constant *Const = IV.isConstant()
      //  ? IV.getConstant() : UndefValue::get(Inst->getType());
      //DEBUG(dbgs() << "  Constant: " << *Const << " = " << *Inst);

      // Replaces all of the uses of a variable with uses of the constant.
      //Inst->replaceAllUsesWith(Const);
      
      // Delete the instruction.
      if(IV.isUntainted() || IV.isBottom()){
	Inst->eraseFromParent();
      // Hey, we just changed something!
      MadeChanges = true;
      ++NumInstRemoved;
      }
    }
  }

  return MadeChanges;
}

namespace {
  //===--------------------------------------------------------------------===//
  //
  /// IPTaint Class - This class implements interprocedural Taint
  /// Propagation.
  ///
  struct IPTaint : public ModulePass {
    static char ID;
    IPTaint() : ModulePass(ID) {
      //initializeIPSCCPPass(*PassRegistry::getPassRegistry());
    }
    bool runOnModule(Module &M);
  };
} // end anonymous namespace

char IPTaint::ID = 0;
//static RegisterPass<Taint> X("taint", "Taint Propagation", false, false);
static RegisterPass<IPTaint> Y("iptaint","Interprocedural Taint Propagation",false, false);


static bool AddressIsTaken(const GlobalValue *GV) {
  // Delete any dead constantexpr klingons.
  GV->removeDeadConstantUsers();

  for (Value::const_use_iterator UI = GV->use_begin(), E = GV->use_end();
       UI != E; ++UI) {
    const User *U = *UI;
    if (const StoreInst *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getOperand(0) == GV || SI->isVolatile())
        return true;  // Storing addr of GV.
    } else if (isa<InvokeInst>(U) || isa<CallInst>(U)) {
      // Make sure we are calling the function, not passing the address.
      ImmutableCallSite CS(cast<Instruction>(U));
      if (!CS.isCallee(UI))
        return true;
    } else if (const LoadInst *LI = dyn_cast<LoadInst>(U)) {
      if (LI->isVolatile())
        return true;
    } else if (isa<BlockAddress>(U)) {
      // blockaddress doesn't take the address of the function, it takes addr
      // of label.
    } else {
      return true;
    }
  }
  return false;
}

bool IPTaint::runOnModule(Module &M) {
  TaintSolver Solver(getAnalysisIfAvailable<TargetData>());

  // AddressTakenFunctions - This set keeps track of the address-taken functions
  // that are in the input.  As IPTaint runs through and simplifies code,
  // functions that were address taken can end up losing their
  // address-taken-ness.  Because of this, we keep track of their addresses from
  // the first pass so we can use them for the later simplification pass.
  SmallPtrSet<Function*, 32> AddressTakenFunctions;
  
  // Loop over all functions, marking arguments to those with their addresses
  // taken or that are external as may be tainted.
  //
  for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
    if (F->isDeclaration())
      continue;
    
    // If this is a strong or ODR definition of this function, then we can
    // propagate information about its result into callsites of it.
    if (!F->mayBeOverridden())
      Solver.AddTrackedFunction(F);
    
    // If this function only has direct calls that we can see, we can track its
    // arguments and return value aggressively, and can assume it is not called
    // unless we see evidence to the contrary.
    if (F->hasLocalLinkage()) {
      if (AddressIsTaken(F))
        AddressTakenFunctions.insert(F);
      else {
        Solver.AddArgumentTrackedFunction(F);
        continue;
      }
    }

    // Assume the function is called.
    Solver.MarkBlockExecutable(F->begin());
    
    // Assume nothing about the incoming arguments.
    for (Function::arg_iterator AI = F->arg_begin(), E = F->arg_end();
         AI != E; ++AI)
      Solver.markAnythingmaybetainted(AI);
  }

  // Loop over global variables.  We inform the solver about any internal global
  // variables that do not have their 'addresses taken'.  If they don't have
  // their addresses taken, we can propagate taint through them.
  for (Module::global_iterator G = M.global_begin(), E = M.global_end();
       G != E; ++G)
    if (!G->isConstant() && G->hasLocalLinkage() && !AddressIsTaken(G))
      Solver.TrackValueOfGlobalVariable(G);

  // Solve for untainted.
  bool ResolvedUndefs = true;
  while (ResolvedUndefs) {
    Solver.Solve();

    DEBUG(dbgs() << "RESOLVING UNDEFS\n");
    ResolvedUndefs = false;
    for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F)
      ResolvedUndefs |= Solver.ResolvedUndefsIn(*F);
  }

  bool MadeChanges = false;

  // Iterate over all of the instructions in the module, removing them 
  // if we have found them to be of taint_not values.
  //
  SmallVector<BasicBlock*, 512> BlocksToErase;

  for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
    if (Solver.isBlockExecutable(F->begin())) {
      for (Function::arg_iterator AI = F->arg_begin(), E = F->arg_end();
           AI != E; ++AI) {
        if (AI->use_empty() || AI->getType()->isStructTy()) continue;
        
        // TODO: Could use getStructLatticeValueFor to find out if the entire
        // result is a constant and replace it entirely if so.

        LatticeVal IV = Solver.getLatticeValueFor(AI);
        if (IV.isTainted()) continue;
        
        //Constant *CST = IV.isConstant() ?
        //IV.getConstant() : UndefValue::get(AI->getType());
        //DEBUG(dbgs() << "***  Arg " << *AI << " = " << *CST <<"\n");
        
        // Replaces all of the uses of a variable with uses of the
        // constant.
        //AI->replaceAllUsesWith(CST);
        ++IPNumArgsTainted;
      }
    }

    for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
      if (!Solver.isBlockExecutable(BB)) {
        DeleteInstructionInBlock(BB);
        MadeChanges = true;

        TerminatorInst *TI = BB->getTerminator();
        for (unsigned i = 0, e = TI->getNumSuccessors(); i != e; ++i) {
          BasicBlock *Succ = TI->getSuccessor(i);
          if (!Succ->empty() && isa<PHINode>(Succ->begin()))
            TI->getSuccessor(i)->removePredecessor(BB);
        }
        //if (!TI->use_empty())
        //  TI->replaceAllUsesWith(UndefValue::get(TI->getType()));
        TI->eraseFromParent();

        if (&*BB != &F->front())
          BlocksToErase.push_back(BB);
        else
          new UnreachableInst(M.getContext(), BB);
        continue;
      }
      
      for (BasicBlock::iterator BI = BB->begin(), E = BB->end(); BI != E; ) {
        Instruction *Inst = BI++;
        if (Inst->getType()->isVoidTy() || Inst->getType()->isStructTy())
          continue;
        
        // TODO: Could use getStructLatticeValueFor to find out if the entire
        // result is a untainted and delete it entirely if so.
        
        LatticeVal IV = Solver.getLatticeValueFor(Inst);
        if (IV.isTainted())
          continue;
        
        //Constant *Const = IV.isConstant()
        //  ? IV.getConstant() : UndefValue::get(Inst->getType());
        //DEBUG(dbgs() << "  Constant: " << *Const << " = " << *Inst);

        // Replaces all of the uses of a variable with uses of the
        // constant.
        //Inst->replaceAllUsesWith(Const);
        
        // Delete the instruction.
        if (!isa<CallInst>(Inst) && !isa<TerminatorInst>(Inst))
          Inst->eraseFromParent();

        // Hey, we just changed something!
        MadeChanges = true;
        ++IPNumInstRemoved;
      }
    }

    // Now that all instructions in the function are constant folded, erase dead
    // blocks, because we can now use ConstantFoldTerminator to get rid of
    // in-edges.
    for (unsigned i = 0, e = BlocksToErase.size(); i != e; ++i) {
      // If there are any PHI nodes in this successor, drop entries for BB now.
      BasicBlock *DeadBB = BlocksToErase[i];
      for (Value::use_iterator UI = DeadBB->use_begin(), UE = DeadBB->use_end();
           UI != UE; ) {
        // Grab the user and then increment the iterator early, as the user
        // will be deleted. Step past all adjacent uses from the same user.
        Instruction *I = dyn_cast<Instruction>(*UI);
        do { ++UI; } while (UI != UE && *UI == I);

        // Ignore blockaddress users; BasicBlock's dtor will handle them.
        if (!I) continue;

        bool Folded = ConstantFoldTerminator(I->getParent());
        if (!Folded) {
          // The constant folder may not have been able to fold the terminator
          // if this is a branch or switch on undef.  Fold it manually as a
          // branch to the first successor.
#ifndef NDEBUG
          if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
            assert(BI->isConditional() && isa<UndefValue>(BI->getCondition()) &&
                   "Branch should be foldable!");
          } else if (SwitchInst *SI = dyn_cast<SwitchInst>(I)) {
            assert(isa<UndefValue>(SI->getCondition()) && "Switch should fold");
          } else {
            llvm_unreachable("Didn't fold away reference to block!");
          }
#endif
          
          // Make this an uncond branch to the first successor.
          TerminatorInst *TI = I->getParent()->getTerminator();
          BranchInst::Create(TI->getSuccessor(0), TI);
          
          // Remove entries in successor phi nodes to remove edges.
          for (unsigned i = 1, e = TI->getNumSuccessors(); i != e; ++i)
            TI->getSuccessor(i)->removePredecessor(TI->getParent());
          
          // Remove the old terminator.
          TI->eraseFromParent();
        }
      }

      // Finally, delete the basic block.
      F->getBasicBlockList().erase(DeadBB);
    }
    BlocksToErase.clear();
  }

  // If we inferred constant or undef return values for a function, we replaced
  // all call uses with the inferred value.  This means we don't need to bother
  // actually returning anything from the function.  Replace all return
  // instructions with return undef.
  //
  // Do this in two stages: first identify the functions we should process, then
  // actually zap their returns.  This is important because we can only do this
  // if the address of the function isn't taken.  In cases where a return is the
  // last use of a function, the order of processing functions would affect
  // whether other functions are optimizable.
  SmallVector<ReturnInst*, 8> ReturnsToZap;
  
  // TODO: Process multiple value ret instructions also.
  const DenseMap<Function*, LatticeVal> &RV = Solver.getTrackedRetVals();
  for (DenseMap<Function*, LatticeVal>::const_iterator I = RV.begin(),
       E = RV.end(); I != E; ++I) {
    Function *F = I->first;
    if (I->second.isTainted() || F->getReturnType()->isVoidTy())
      continue;
  
    // We can only do this if we know that nothing else can call the function.
    if (!F->hasLocalLinkage() || AddressTakenFunctions.count(F))
      continue;
    
    for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB)
      if (ReturnInst *RI = dyn_cast<ReturnInst>(BB->getTerminator()))
        if (!isa<UndefValue>(RI->getOperand(0)))
          ReturnsToZap.push_back(RI);
  }

  // Zap all returns which we've identified as zap to change.
  for (unsigned i = 0, e = ReturnsToZap.size(); i != e; ++i) {
    Function *F = ReturnsToZap[i]->getParent()->getParent();
    ReturnsToZap[i]->setOperand(0, UndefValue::get(F->getReturnType()));
  }
    
  // If we inferred constant or undef values for globals variables, we can delete
  // the global and any stores that remain to it.
  const DenseMap<GlobalVariable*, LatticeVal> &TG = Solver.getTrackedGlobals();
  for (DenseMap<GlobalVariable*, LatticeVal>::const_iterator I = TG.begin(),
         E = TG.end(); I != E; ++I) {
    GlobalVariable *GV = I->first;
    assert(!I->second.Tainted() &&
           "Tainted values should have been taken out of the map!");
    DEBUG(dbgs() << "Found that GV '" << GV->getName() << "' is constant!\n");
    while (!GV->use_empty()) {
      StoreInst *SI = cast<StoreInst>(GV->use_back());
      SI->eraseFromParent();
    }
    M.getGlobalList().erase(GV);
    ++IPNumGlobalTaint;
  }

  return MadeChanges;
}
