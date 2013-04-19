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
