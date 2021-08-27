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

#include <list>
#include <string>
#include <fstream>
#include <vector>
#include <map>
#include <set>

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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) {
	char* instWhiteListFilename = getenv("AFL_INST_WHITELIST");
        if (instWhiteListFilename) {
          std::ifstream fileStream;
          fileStream.open(instWhiteListFilename);
          if (!fileStream) report_fatal_error("Unable to open AFL_INST_WHITELIST");

          std::string line;
          getline(fileStream, line);
          while (fileStream) {
            myWhitelist.push_back(line);
            getline(fileStream, line);
          }
        }

	char * path_count_str = getenv("AFL_PATH_COUNT");
	if (path_count_str) {
	  path_count = 2;
	  sscanf(path_count_str, "%u", &path_count);
	  if (path_count < 2) path_count = 2;
	  if (path_count > LLVM_MAX_LOC_COUNT) path_count = LLVM_MAX_LOC_COUNT;
	} else {
	  path_count = 2;
	}
      }

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

    bool getInstFileName(Instruction * IP, std::string & filename) {
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

	    filename = instFilename.str();

	    return true;
	  } else {
	  return false;
	}      
    }

    bool checkInWhiteList(const std::string & filename) {
      /* Continue only if we know where we actually are */
      if (!myWhitelist.empty()) {
	/* If whitelist is not empty, we only insert inst into files in list. */
	
	for (std::list<std::string>::iterator it = myWhitelist.begin(); it != myWhitelist.end(); ++it) {
	  /* We don't check for filename equality here because
	   * filenames might actually be full paths. Instead we
	   * check that the actual filename ends in the filename
	   * specified in the list. */
	  if (filename.length() >= it->length() && it->length() > 0) {
	    if (filename.compare(filename.length() - it->length(), it->length(), *it) == 0) {
	      return true;
	    }
	  }
	}

	/* If file name is not in list, then do nothing. */
	return false;
      }

      return true;
    }
    
  protected:
    std::list<std::string> myWhitelist;

    int path_count;
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
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc"
      , 0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevFileId =
    new GlobalVariable(
		       M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_file_id"
		       // );
		       , 0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevLocsPtr =
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_prev_locs"
			 // );
			 , 0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLCurIndex = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_cur_index"
						   // );
      , 0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLAreaIndex = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_area_index"
						    // );
      , 0, GlobalVariable::GeneralDynamicTLSModel, 0, false);  
  

  /* Instrument all the things! */

  int inst_blocks = 0;

  std::vector<BasicBlock*> BasicBlocksToInsert;
  std::map<BasicBlock*, unsigned int> basicBlockLocId;
  std::map<BasicBlock*, unsigned int> basicBlockFileNameId;
  std::set<std::string> filenameSet;
  
  for (auto &F : M) {
    for (auto &BB : F) {
      std::string filename;
      BasicBlock::iterator IP = BB.getFirstInsertionPt();

      if (!getInstFileName(&*IP, filename)) continue;
      if (!checkInWhiteList(filename)) continue;
      if (AFL_R(100) >= inst_ratio) continue;

      filenameSet.insert(filename);
      BasicBlocksToInsert.push_back(&BB);
      basicBlockLocId[&BB] = AFL_R(MAP_SIZE);
      basicBlockFileNameId[&BB] = custom_hash(filename.c_str());
    }
  }

  /* Normal: update previous file id and previous loc. */
  for (auto BB : BasicBlocksToInsert) {
    BasicBlock::iterator IP = BB->getFirstInsertionPt();
    IRBuilder<> IRB(&(*IP));

    unsigned int cur_loc = basicBlockLocId[BB];
    unsigned int file_name_hash = basicBlockFileNameId[BB];

    ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
    ConstantInt *CurFileId = ConstantInt::get(Int32Ty, file_name_hash);

    LoadInst * PrevFileId = IRB.CreateLoad(AFLPrevFileId);
    LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);

    PrevFileId->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

    StoreInst *Store =
      IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
    StoreInst *StoreFileId =
      IRB.CreateStore(ConstantInt::get(Int32Ty, file_name_hash), AFLPrevFileId);
    
    Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    StoreFileId->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  }
  
  /* Add If branch: when filename is different from the previous one. */
  
  for (auto BB : BasicBlocksToInsert) {
    BasicBlock::iterator IP = BB->getFirstInsertionPt();
    IRBuilder<> IRB(&(*IP));

    unsigned int cur_loc = basicBlockLocId[BB];
    unsigned int file_name_hash = basicBlockFileNameId[BB];

    ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
    ConstantInt *CurFileId = ConstantInt::get(Int32Ty, file_name_hash);

    LoadInst * PrevFileId = IRB.CreateLoad(AFLPrevFileId);
    LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);

    PrevFileId->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


    // Only when prevFileId != curFileId, do the following:
    
    auto thenInst = SplitBlockAndInsertIfThen(IRB.CreateICmpNE(PrevFileId, CurFileId), &(*IP), false);

#define  IRB IRBthen
    // edge_id = cur_loc ^ prev_loc
    // old = prev_locs[cur_index]
    // new_area_index = area_index >> 2 ^ edge_id ^ (old >> 2 * COUNT)
    // ++ area[new_area_index]
    // cur_index = (++ cur_index) % COUNT
    // area_index = new_area_index
    
    IRBuilder<> IRBthen(thenInst);

    PrevFileId = IRBthen.CreateLoad(AFLPrevFileId);
    PrevLoc = IRBthen.CreateLoad(AFLPrevLoc);
    LoadInst * CurIndex = IRBthen.CreateLoad(AFLCurIndex);
    LoadInst * AreaIndex = IRBthen.CreateLoad(AFLAreaIndex);
    LoadInst * PrevLocsPtr = IRBthen.CreateLoad(AFLPrevLocsPtr);
    LoadInst *MapPtr = IRBthen.CreateLoad(AFLMapPtr);

    PrevFileId ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    PrevLoc    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    CurIndex   ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    AreaIndex  ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    PrevLocsPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    MapPtr     ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    
    Value *PrevLocCasted = IRBthen.CreateZExt(PrevLoc, IRBthen.getInt32Ty());
    Value *CurEdgeId = IRBthen.CreateXor(CurLoc, PrevLocCasted); // edge_id = cur_loc ^ prev_loc
    Value *OldPtrIdx    = IRBthen.CreateGEP(PrevLocsPtr, CurIndex);
    LoadInst * Old = IRBthen.CreateLoad(OldPtrIdx);              // old     = prev_locs[cur_index]

    Old        ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    
    Value * newAreaIndex = IRBthen.CreateXor(IRBthen.CreateXor(IRBthen.CreateLShr(AreaIndex, ConstantInt::get(Int32Ty, 2)),
							       IRBthen.CreateLShr(Old, ConstantInt::get(Int32Ty, 2 * path_count))),
					     CurEdgeId);

    Value *MapPtrIdx = IRBthen.CreateGEP(MapPtr, newAreaIndex);

    LoadInst *Counter = IRBthen.CreateLoad(MapPtrIdx);
    Counter    ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

    Value *Incr = IRBthen.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));

    IRBthen.CreateStore(Incr, MapPtrIdx)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None)); // ++ area[area_index]
    IRBthen.CreateStore(CurEdgeId, OldPtrIdx)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None)); // prev_locs[cur_index] = edge_id
    IRBthen.CreateStore(newAreaIndex, AFLAreaIndex)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None)); // area_index = new_area_index

    Value *Neq = IRBthen.CreateICmpNE(CurIndex, ConstantInt::get(Int32Ty, path_count - 1));
    Value *CurIndexNew = IRBthen.CreateMul(IRBthen.CreateAdd(CurIndex, ConstantInt::get(Int32Ty, 1)),
    					   IRBthen.CreateZExt(Neq, IRBthen.getInt32Ty()));
    
    IRBthen.CreateStore(CurIndexNew, AFLCurIndex)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

#undef   IRB
  }

  inst_blocks += BasicBlocksToInsert.size();

  /* Say something nice. */

  if (!be_quiet) {
 
    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

    fprintf(stderr, "[filenames]: ");
    for (const auto & filename : filenameSet) {
      fprintf(stderr, "%s,", filename.c_str());
    }
    fprintf(stderr, "\n");
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
