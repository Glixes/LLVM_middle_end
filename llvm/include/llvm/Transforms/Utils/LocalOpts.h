#ifndef LLVM_TRANSFORMS_LOCALOPTS_H
#define LLVM_TRANSFORMS_LOCALOPTS_H

#include "llvm/IR/PassManager.h"
#include <llvm/IR/Constants.h>

namespace llvm 
{

    class LocalOpts : public PassInfoMixin<LocalOpts> {
    public:
        PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };

    /** @class describing a binary operation
     * Provided accessibility to costant values in the operation
     * and concepts like first constant present or opposite operation
    */
    class Operation 
    {
        public: 
            Instruction *inst;  // the llvm instruction object
            Value* register1;   // the left register
            Value* register2;   // the right register
            ConstantInt *C1;    // the left register casted to constant integer, if possible
            ConstantInt *C2;    // the right register casted to constant integer, if possible
            unsigned int op;    // the operation code

            /** @brief Operation class constructor
             * 
             * @param inst is the instruction that represents the operation
             * Builds an object of the class describes a binary operation
             * Attributes C1 and C2 contain the result of the cast to integer constant, if the cast fails they contain nullptr
            */
            Operation(Instruction &inst);

            /** @brief Get the number of integer constants in the operation
             * 
             * @return integer number of constants
            */
            size_t getNConstants();

            /** @brief Get the SSA register in the opposite position of the specified constant integer, if present
             * 
             * @param C is the constant integer
             * @return the register, or nullptr if the constant is not present
            */
            Value* getOpposite(ConstantInt *C);

            /** @brief Get the first integer constant starting from the left operand
             * 
             * @return the first constant present, or the right constant; if also the right constant is absent, return nullptr
            */
            ConstantInt* getFirstConstantInt();

            bool isOppositeOp(Operation *x);
            Instruction* getRegThatIsResult(Operation *x);

            /** @brief Determine if the operation is valid for local optmizations
             * Operations need to have at least a constant and in case of subtractions and divisions it must be as second operand
             * 
             * @return true or false
            */
            bool isValidForOpt();
    };

} // namespace llvm
#endif // LLVM_TRANSFORMS_LOCALOPTS_H

