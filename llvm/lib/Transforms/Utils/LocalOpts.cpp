//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
// #include <llvm/IR/Constants.h>

using namespace llvm;

Operation::Operation(Instruction &inst) : register1(inst.getOperand(0)), register2(inst.getOperand(1)), 
  inst(&inst), C1(dyn_cast<ConstantInt>(register1)), C2(dyn_cast<ConstantInt>(register2)), 
  op(inst.getOpcode()) {}

size_t Operation::getNConstants ()
{
  size_t counter = 0;
  if (C1)
    counter++;
  if (C2)
    counter++;
  return counter;
}

Value* Operation::getOpposite (ConstantInt *C)
{
  if (C == C1)
    return register2;
  else if (C == C2)
    return register1;
  return nullptr;
}

ConstantInt* Operation::getFirstConstantInt ()
{
  return (C1) ? C1 : C2;
}

/** @brief Check for algebraic identity and in positive cases, return the instruction to replace.
 * 
 * @param operands ConstantInt operands
 * @param inst instruction examined
 * @return Value containing the intruction to replace, nullptr otherwise.
*/
Value* getAlgebraicIdentity (Operation *o)
{
  ConstantInt* C = nullptr;
  switch (o->op)
  {
    case BinaryOperator::Add:
      if (o->C1 && o->C1->isZero())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::Sub:
      if (o->C2 && o->C2->isZero())
        C = o->C2;
      break;

    case BinaryOperator::Mul:
      if (o->C1 && o->C1->isOne())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
      if (o->C2 && o->C2->isOne())
        C = o->C2;
      break;
  }

  return (C) ? o->getOpposite(C) : nullptr;
}

Instruction* getStrengthReduction (Operation *o)
{
  ConstantInt *C = o->getFirstConstantInt();
  // Negative constants are not handled
  unsigned int shiftVal = C->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(C->getType(), shiftVal);

  Instruction* newinst = nullptr;
  switch (o->op)
  {
      case BinaryOperator::Mul:
      {
        Instruction *shli = BinaryOperator::Create(Instruction::Shl, o->getOpposite(C), shift);
        shli->insertAfter(o->inst);
        outs() << "C = " << C->getValue().getSExtValue() << "\n";
        unsigned int restVal = (2 << shiftVal) - C->getValue().getSExtValue();
        if (restVal == 0)
        {
          newinst = shli;
          break;
        }
        ConstantInt *rest = ConstantInt::get(C->getType(), restVal);
        if (restVal > 1)
        {
          Instruction *muli = BinaryOperator::Create(BinaryOperator::Mul, o->getOpposite(C), rest);
          muli->insertAfter(shli);
          newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, muli);
          newinst->insertAfter(muli);
          break;
        }
        newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, rest);
        newinst->insertAfter(shli);
        break;
      }

      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
      {
        if (C != o->C2 && C->getValue().isPowerOf2())
          break;
        newinst = BinaryOperator::Create(Instruction::LShr, o->getOpposite(C), shift);
        newinst->insertAfter(o->inst);
        break;
      }
  }

  return newinst;
}

bool runOnBasicBlock(BasicBlock &B) 
{
  for (auto &inst : B) 
  {
    // check for binary operations
    if (!inst.isBinaryOp())
      continue;

    outs() << "Sono la istruzione: " << inst << "\n";

    Operation *o = new Operation (inst);
    if (o->getNConstants() == 0)
      continue;
    // TO DO handle constant folding

    /* Optimized instruction.
    * The Value type is necessary in order to include also the Argument objects (representig
    * function's arguments).
    */
    outs() << "Sto provando l'algebraic identity\n";
    Value *i = getAlgebraicIdentity(o);
    if (!i){
      outs() << "Sto provando la strength reduction\n";
      i = getStrengthReduction(o);}

    // replace the non-optimized instruction uses with the optimized ones
    if (i)
      inst.replaceAllUsesWith(i);
  }

  return true;
}

bool runOnFunction(Function &F) {
  bool Transformed = false;

  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}

PreservedAnalyses LocalOpts::run(Module &M, ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();

  return PreservedAnalyses::all();
}