#ifndef LLVM_TRANSFORMS_LOCALOPTS_H
#define LLVM_TRANSFORMS_LOCALOPTS_H

#include "llvm/IR/PassManager.h"
#include <llvm/IR/Constants.h>

namespace llvm {
class LocalOpts : public PassInfoMixin<LocalOpts> {
public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

class Operation 
{
    private:
        Value* register1;
        Value* register2;
        
    public: 
        Instruction *inst;
        ConstantInt *C1;
        ConstantInt *C2;
        unsigned int op;
        Operation(Instruction &inst);
        size_t getNConstants();
        Value* getOpposite(ConstantInt *C);
        ConstantInt* getFirstConstantInt();
};
} // namespace llvm
#endif // LLVM_TRANSFORMS_LOCALOPTS_H

