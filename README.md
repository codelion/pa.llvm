pa.llvm
=======

Program Analysis for LLVM

Need LLVM Source Code to Run
- copy in lib/Transforms/ folder inside LLVM top level source tree
- configure using ./configure in source root directory
- compile using "gmake" command in local directory
- should get a “Debug+Asserts/lib/CVA.so” under the top level directory of the LLVM source tree
- run using opt -load ../../../Debug+Asserts/lib/CVA.so -CVA < bitcode.bc > /dev/null

Details on LLVM Pass can be found at http://llvm.org/docs/WritingAnLLVMPass.html

Publications
------------
[An Empirical Study of Path Feasibility Queries] (http://arxiv.org/abs/1302.4798), CoRR 2013

A Critical Review of Dynamic Taint Analysis and Forward Symbolic Execution, Technical Report NUS 2012

