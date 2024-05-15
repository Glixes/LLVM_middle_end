#ifndef LLVM_TRANSFORMS_LOOPOPT_H
#define LLVM_TRANSFORMS_LOOPOPT_H

#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include <llvm/IR/Constants.h>

namespace llvm 
{
    class LoopOpt : public PassInfoMixin<LoopOpt> {
    public:
        PreservedAnalyses run(Loop &L,LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR, LPMUpdater &LU);
    };
} // namespace llvm
#endif // LLVM_TRANSFORMS_LOCALOPTS_H

