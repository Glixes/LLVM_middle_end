#ifndef LLVM_TRANSFORMS_TESTPASS_H
#define LLVM_TRANSFORMS_TESTPASS_H

#include "llvm/IR/PassManager.h"

namespace llvm {
class TestPass : public PassInfoMixin<TestPass> {
public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};
} // namespace llvm
#endif // LLVM_TRANSFORMS_TESTPASS _H

