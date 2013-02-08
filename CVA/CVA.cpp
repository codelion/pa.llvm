// Change Value Analysis
// Finds the instructions changed by a change in value of an input variable
//
#define DEBUG_TYPE "cva"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/InstIterator.h"
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

STATISTIC(NumInstChanged, "Number of Instructions Changed");
STATISTIC(NumInstUnchanged, "Number of Instructions Unchanged");
STATISTIC(NumInstUndef, "Number of Instructions Undefined");
//STATISTIC(NumInstDel, "Number of Instructions Deleted");

namespace {
/// LatticeVal class - This class represents the different lattice values that
/// an LLVM value may occupy.  It is a simple class with value semantics.
///
class LatticeVal {
  enum LatticeValueTy {
    /// ch - This LLVM Value may be Changed.
    ch,
    
    /// unch - This LLVM Value is Unchanged.
    unch,

    /// undef - This LLVM Value is Undefined.
    undef    
  };

  /// Val: This stores the current lattice value 
  LatticeValueTy Val;
  
public:
  LatticeVal() : Val(undef) {}
  
  LatticeValueTy getLatticeValue() const {
    return Val;
  }
  
  bool isUndefined() const { return getLatticeValue() == undef; }
  bool isUnchanged() const {
    return getLatticeValue() == unch ;
  }
  bool isChanged() const { return getLatticeValue() == ch; }

  /// markUndef - Return true if this is a change in status.
  bool markUndefined() {
    if (isUndefined())
      return false;
    if (isUnchanged())
      Val = undef;
    else assert(getLatticeValue() == ch && "Cannot move from ch to undef!");
    return true;
  }

  /// markUnchanged - Return true if this is a change in status.
  bool markUnchanged() {
    if (isUnchanged()) { 
      return false;
    }
    
    if (isUndefined()) {
      Val = unch; // undef to unch
    } else {
      assert(getLatticeValue() == ch && 
             "Cannot move from ch to unch!");
    }
    return true;
  }

  /// markChanged - Return true if this is a change in status.
  bool markChanged() {
    if (isChanged()) { // ch
      return false;
    }
    
    Val = ch;
    return true;
  }
};
} // end anonymous namespace.

//===----------------------------------------------------------------------===//
//
/// Analyzer - This class is a general purpose Analyzer for propagating Changed Values.
///
class Analyzer : public InstVisitor<Analyzer> {
  const TargetData *TD;
  DenseMap<Value*, LatticeVal> ValueState;  // The state each value is in.
  SmallVector<Value*, 64> InstWorkList; // Worklist of all instructions
  SmallVector<Value*, 64> ChInstWorkList; // Worklist of Changed instructions

  public:
    Analyzer(const TargetData *td) : TD(td) {}

    LatticeVal getLatticeValueFor(Value *V) const {
      DenseMap<Value*, LatticeVal>::const_iterator I = ValueState.find(V);
      assert(I != ValueState.end() && "V is not in valuemap!");
      return I->second;
    } 

//Marks an instruction as changed and inserts it to the worklist
    void markChanged(Value *V){
      if(ValueState[V].markChanged()) 
        ChInstWorkList.push_back(V);
    }

//To be used to mark undefined instructions as unchanged if they do not change 
//and insert back into worklist
    void markUnchanged(Value *V){
      if(ValueState[V].markUnchanged())
	InstWorkList.push_back(V);
    }

//To be used initally only to mark all instructions as undefined 
    void markUndefined(Value *V) {
      std::pair<DenseMap<Value*, LatticeVal>::iterator, bool> I = 
                                 ValueState.insert(std::make_pair(V, LatticeVal()));
      if(I.second) InstWorkList.push_back(V);
      else ValueState[V].markUndefined();
    }

// Perform the Constant Value Analysis for the instructions in the worklist
    void RunAnalysis();

  private:

  // OperandChangedState - This method is invoked on all of the users of an
  // instruction that was just changed state somehow.  Based on this
  // information, we need to update the specified user of this instruction.
  //
  void OperandChangedState(Instruction *I) {
    visit(*I);
  }

  private:
    friend class InstVisitor<Analyzer>;

// visit implementations - Something changed in this instruction.  Either an
  // operand made a transition, or the instruction is newly executable.  Change
  // the value type of I to reflect these changes if appropriate.
  void visitPHINode(PHINode &I) { markChanged(&I); }

  // Terminators
  void visitReturnInst(ReturnInst &I) { markChanged(&I); }
  void visitTerminatorInst(TerminatorInst &TI) { markChanged(&TI); }

  void visitCastInst(CastInst &I) { markChanged(&I); }
  void visitSelectInst(SelectInst &I) { markChanged(&I); }
  void visitBinaryOperator(Instruction &I) { markChanged(&I); }
  void visitCmpInst(CmpInst &I) { markChanged(&I); }
  void visitExtractElementInst(ExtractElementInst &I) { markChanged(&I); }
  void visitInsertElementInst(InsertElementInst &I) { markChanged(&I); }
  void visitShuffleVectorInst(ShuffleVectorInst &I) { markChanged(&I); }
  void visitExtractValueInst(ExtractValueInst &EVI) { markChanged(&EVI); }
  void visitInsertValueInst(InsertValueInst &IVI) { markChanged(&IVI); }
  void visitLandingPadInst(LandingPadInst &I) { markChanged(&I); }

  // Instructions that cannot be folded away.
  void visitStoreInst     (StoreInst &I) { markChanged(&I); }
  void visitLoadInst      (LoadInst &I) { markChanged(&I); }
  void visitGetElementPtrInst(GetElementPtrInst &I) { markChanged(&I); }
  void visitCallInst      (CallInst &I) {
    visitCallSite(&I);
    markChanged(&I);
  }
  void visitInvokeInst    (InvokeInst &II) {
    visitCallSite(&II);
    visitTerminatorInst(II);
  }
  void visitCallSite      (CallSite CS) {  }

  void visitResumeInst    (TerminatorInst &I) { markChanged(&I); }
  void visitUnwindInst    (TerminatorInst &I) { markChanged(&I); }
  void visitUnreachableInst(TerminatorInst &I) { markChanged(&I); }
  void visitFenceInst     (FenceInst &I) { markChanged(&I); }

  void visitAtomicCmpXchgInst (AtomicCmpXchgInst &I) { markChanged(&I); }
  void visitAtomicRMWInst (AtomicRMWInst &I) { markChanged(&I); }
  void visitAllocaInst    (Instruction &I) { markChanged(&I); }
  void visitVAArgInst     (Instruction &I) { markChanged(&I); }

  void visitInstruction(Instruction &I) {
    // If a new instruction is added to LLVM that we don't handle.
    dbgs() << "CVA: Don't know how to handle: " << I;
    markChanged(&I);   // Just in case
  }
};

void Analyzer::RunAnalysis(){
  // Process the work lists until they are empty
  while (!InstWorkList.empty() || !ChInstWorkList.empty()) {
    while(!ChInstWorkList.empty()) {
      Value *I = ChInstWorkList.pop_back_val();

      DEBUG(dbgs() << "\nPopped off ChI-WL: " << *I << '\n');
      // Instruction 'I' got into this worklist because it made a transition from (undef or unch) to ch
      // All users of this instruction have to be visited to progate this change
      for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
           UI != E; ++UI)
	 if (Instruction *I = dyn_cast<Instruction>(*UI))
            OperandChangedState(I);
    }
    while(!InstWorkList.empty()) {
      Value *I = InstWorkList.pop_back_val();

      DEBUG(dbgs() << "\nPopped off I-WL: " << *I << '\n');
      // Instruction 'I' got into this worklist because it made a transition from undef to unch
      // propagate this change to the uses of this instruction
      for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
           UI != E; ++UI)
	if (Instruction *I = dyn_cast<Instruction>(*UI))
          OperandChangedState(I);
    }
  }
}

namespace {

  struct CVA : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CVA() : FunctionPass(ID) {}

    // runOnFunction - Run the Change Value Analysis
    // and return true if the function was modified.
    //
    virtual bool runOnFunction(Function &F);
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<AliasAnalysis>();
      AU.addPreserved<AliasAnalysis>();
    }
  private:
    AliasAnalysis *AA;       // Current AliasAnalysis information
    bool MadeChanges;
  };
} // end anonymous namespace

char CVA::ID = 0;
static RegisterPass<CVA> X("cva", "Change Value Analysis", false, false);

bool CVA::runOnFunction(Function &F) {
  DEBUG(dbgs() << "Change Value Analysis on function '" << F.getName() << "'\n");
  Analyzer cva(getAnalysisIfAvailable<TargetData>());

  MadeChanges = false;
  AA = &getAnalysis<AliasAnalysis>();
// errs().write_escaped(F.getName()) << '\n';
// By Default we mark all arguments to the function as undef
//  for (Function::arg_iterator AI = F.arg_begin(), E = F.arg_end(); AI != E;++AI)
//    cva.markUndefined(AI);

// By Default we mark all instructions in the function to be undef
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
  {
     if (isa<ReturnInst>(*I))
	cva.markChanged(&*I); // mark all return values to be changed instead
  }

// Now mark some of the variables as changed
// By Default we mark all the uses of the arguments to the function as changed
/*  for (Function::arg_iterator AI = F.arg_begin(), E = F.arg_end(); AI != E;++AI)
  {    //cva.markChanged(AI);

    for (Value::use_iterator i = AI->use_begin(), e = AI->use_end(); i != e; ++i)
      if (Instruction *Inst = dyn_cast<Instruction>(*i)) {
        //errs() << "Argument is used in instruction:\n";
        //errs() << *Inst << "\n";
        cva.markChanged(Inst);
      }
  }
*/

  cva.RunAnalysis();

//After Analysis Update Stats
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){
    LatticeVal IV = cva.getLatticeValueFor(&*I);
    if(IV.isChanged()) ++NumInstChanged;
    else if(IV.isUnchanged()) ++NumInstUnchanged;
    else ++NumInstUndef;
  }

//Remove unreachable and unchanged instructions which can be removed
//Cannot remove structuretype, call inst, terminator inst

  for (inst_iterator Inst = inst_begin(F), E = inst_end(F); Inst != E; ++Inst){
    Instruction *I = &*Inst;
    //errs() << *Inst << "\n";
    //if (isa<LoadInst>(*I) || isa<StoreInst>(*I)|| isa<AllocaInst>(*I) || I->getType()-> isVoidTy() || isa<TerminatorInst>(*I) || I->getType()->isStructTy() || isa<CallInst>(*I))
    //   continue;
    if (isa<TerminatorInst>(*I) || isa<CallInst>(*I) || isa<LoadInst>(*I) || isa<StoreInst>(*I) || isa<AllocaInst>(*I))
       continue;
      
    //if (isa<StoreInst>(*I) || isa<LoadInst>(*I) || isa<AllocaInst>(*I)){
      //if (isa<StoreInst>(*I)){
 	//BasicBlock::iterator ii(I);
       // ReplaceInstWithValue(I->getParent()->getInstList(),ii,Constant::getNullValue(I->getType()));
      //}
    //  continue;
    //}

    LatticeVal IV = cva.getLatticeValueFor(&*I);
    if(IV.isUnchanged() || IV.isUndefined()){
      //errs() <<"instr: " << *I <<" value: "<< IV.getLatticeValue() <<"\n"; 
      I->replaceAllUsesWith(UndefValue::get(I->getType()));
      //I->removeFromParent();
      //++NumInstDel;
    //for (Value::use_iterator UI = I->use_begin(), E = I->use_end();
    //       UI != E; ++UI)
	//if (Instruction *I = dyn_cast<Instruction>(*UI))
          //    errs()<< "users: " << *I <<" value: "<< cva.getLatticeValueFor(I).getLatticeValue() <<"\n";
      MadeChanges = true; 
    }
  }

  return MadeChanges;
}
