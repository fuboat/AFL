/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

      /* This is a custom hash function to distinguish the input files. */
    static unsigned int custom_hash(const char * s) {
      unsigned int hash_value = 0;
    
      for (; (*s) != 0; ++ s) {
	hash_value = ((unsigned long long) hash_value * 257 + (*s) + 1) % 1000000007;
      }
    
      return hash_value;
    }
  };
}

char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevFuboatLoc =
    new GlobalVariable(
		       M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_fuboat_loc",
		       0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevPrevFuboatLoc =
    new GlobalVariable(
		       M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_prev_fuboat_loc",
		       0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevFileId =
    new GlobalVariable(
		       M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_file_id",
		       0, GlobalVariable::GeneralDynamicTLSModel, 0, false);  

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);
      unsigned int file_name_hash = 0;

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Make up file id */

      DebugLoc Loc = IP->getDebugLoc();
#ifdef LLVM_OLD_DEBUG_API
      if ( !Loc.isUnknown() )
#else
      if ( Loc )
#endif /* LLVM_OLD_DEBUG_API */

	{
#ifdef LLVM_OLD_DEBUG_API
	  DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
	  DILocation oDILoc = cDILoc.getOrigLocation();
	  
	  unsigned int instLine = oDILoc.getLineNumber();
	  StringRef instFilename = oDILoc.getFilename();
	  
	  if (instFilename.str().empty()) {
	    /* If the original location is empty, use the actual location */
	    instFilename = cDILoc.getFilename();
	    instLine = cDILoc.getLineNumber();
	  }
#else
	  DILocation *cDILoc = dyn_cast<DILocation>(Loc.getAsMDNode());

	  unsigned int instLine = cDILoc->getLine();
	  StringRef instFilename = cDILoc->getFilename();

	  if (instFilename.str().empty()) {
	    /* If the original location is empty, try using the inlined location */
	    DILocation *oDILoc = cDILoc->getInlinedAt();
	    if (oDILoc) {
	      instFilename = oDILoc->getFilename();
	      instLine = oDILoc->getLine();
	    }
	  }
#endif /* LLVM_OLD_DEBUG_API */

	  /* Continue only if we know where we actually are */
	  if (!instFilename.str().empty()) {
	    /* If filename is known, set file_name_hash to the hash value of int. */
	    file_name_hash = custom_hash(instFilename.str().c_str());
	    fprintf(stderr, "filename = %s, hash = %u\n", instFilename.str().c_str(), file_name_hash);
	  } 
	}

      fprintf(stderr, "hash = %u\n", file_name_hash);

      ConstantInt *CurFileId = ConstantInt::get(Int32Ty, file_name_hash);
      
      LoadInst * PrevFileId = IRB.CreateLoad(AFLPrevFileId);
      PrevFileId->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevFileIdCasted = IRB.CreateZExt(PrevFileId, IRB.getInt32Ty());
      
      /* Calc $(file_id == previous_file_id) and $(file_id != previous_file_id) */
      Value *Eq    = IRB.CreateICmpEQ(PrevFileIdCasted, CurFileId);
      Value *Neq   = IRB.CreateICmpNE(PrevFileIdCasted, CurFileId);
      Value *Eq8  = IRB.CreateZExt(Eq,  IRB.getInt8Ty());
      Value *Neq8  = IRB.CreateZExt(Neq,  IRB.getInt8Ty());
      Value *Eq32  = IRB.CreateZExt(Eq,  IRB.getInt32Ty());
      Value *Neq32 = IRB.CreateZExt(Neq, IRB.getInt32Ty());
      
      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      LoadInst *PrevPrevFuboatLoc = IRB.CreateLoad(AFLPrevPrevFuboatLoc);
      PrevPrevFuboatLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
      LoadInst *PrevFuboatLoc = IRB.CreateLoad(AFLPrevFuboatLoc);
      PrevFuboatLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
	IRB.CreateGEP(MapPtr, IRB.CreateMul(IRB.CreateXor(CurLoc, IRB.CreateXor(PrevLocCasted, IRB.CreateXor(PrevFuboatLoc, PrevPrevFuboatLoc))), Neq32));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, IRB.CreateMul(ConstantInt::get(Int8Ty, 1), Neq8));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev2 = prev2 * eq + (prev_loc >> 2) * neq */

      StoreInst *StorePrevPrev =
	IRB.CreateStore(IRB.CreateAdd(IRB.CreateMul(PrevPrevFuboatLoc, Eq32),
				      IRB.CreateMul(IRB.CreateLShr(PrevLocCasted, ConstantInt::get(Int32Ty, 2)), Neq32)),
			AFLPrevPrevFuboatLoc);
      StorePrevPrev->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
      /* Set prev = prev * eq + (cur_loc >> 2) * neq */

      StoreInst *StorePrev =
	IRB.CreateStore(IRB.CreateAdd(IRB.CreateMul(PrevFuboatLoc, Eq32),
				      IRB.CreateMul(ConstantInt::get(Int32Ty, cur_loc >> 2), Neq32)),
			AFLPrevFuboatLoc);
      StorePrev->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_file_id to file_name_hash */

      StoreInst *StoreFileId =
	IRB.CreateStore(ConstantInt::get(Int32Ty, file_name_hash), AFLPrevFileId);
      StoreFileId->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {
 
    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
