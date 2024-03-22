#ifndef LLVM_TRANSFORMS_TESTPASS_H
#define LLVM_TRANSFORMS_TESTPASS_H
#include "llvm/IR/PassManager.h"
namespace llvm {
class TestPass : public PassInfoMixin<TestPass> {
public:
PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};
} // namespace llvm
#endif // LLVM_TRANSFORMS_TESTPASS _H
