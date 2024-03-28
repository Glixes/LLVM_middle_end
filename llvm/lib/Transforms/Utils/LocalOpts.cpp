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

/** @brief Create a pair containing conversions of the operands to ConstantInt.
* In case one operand is not a constant, it will be converted to nullptr.
*
* @param val1 first value
* @param val2 second value
* @return a pair containing ConstantsInt objects.
*/
std::pair<ConstantInt*, ConstantInt*> getConstantInt (Value *val1, Value *val2)
{ 
  ConstantInt *C1 = dyn_cast<ConstantInt>(val1);
  ConstantInt *C2 = dyn_cast<ConstantInt>(val2);

  return std::pair<ConstantInt*, ConstantInt*> (C1, C2);
}

/** @brief Check for algebraic identity and in positive cases, return the instruction to replace.
 * 
 * @param operands ConstantInt operands
 * @param inst instruction examined
 * @return Value containing the intruction to replace, nullptr otherwise.
*/
Value* getAlgebraicIdentity (std::pair<ConstantInt*, ConstantInt*> operands, Instruction &inst)
{
  switch (inst.getOpcode())
  {
    case BinaryOperator::Add:
      if (operands.first && operands.first->isZero())
        return inst.getOperand(1);
    case BinaryOperator::Sub:
      if (operands.second && operands.second->isZero())
        return inst.getOperand(0);
      break;

    case BinaryOperator::Mul:
      if (operands.first && operands.first->isOne())
        return inst.getOperand(1);
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
      if (operands.second && operands.second->isOne())
        return inst.getOperand(0);
      break;
  }

  return nullptr;
}

Instruction* getStrengthReductionLeft (ConstantInt *C, Instruction &inst)
{
  unsigned int shiftVal = C->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(C->getType(), shiftVal);

  if (inst.getOpcode() != BinaryOperator::Mul)
    return nullptr;

  Value* shli = BinaryOperator::Create(Instruction::Shl, inst.getOperand(0), shift);
  Instruction *newshli = dyn_cast<Instruction>(shli);
  newshli->insertAfter(&inst);
  unsigned int restVal = C->getValue().getSExtValue() - (2 << shiftVal);
  ConstantInt *rest = ConstantInt::get(C->getType(), restVal);
  Value* subi = BinaryOperator::Create(BinaryOperator::Sub, inst.getOperand(1), rest);
  Instruction *newsubi = dyn_cast<Instruction>(subi);
  newsubi->insertAfter(newshli);
  return newsubi;
}

Instruction* getStrengthReductionRight (ConstantInt *C, Instruction &inst)
{
  unsigned int shiftVal = C->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(C->getType(), shiftVal);

  Instruction* newinst = nullptr;
  switch (inst.getOpcode())
  {
      case BinaryOperator::Mul:
        Value* shli = BinaryOperator::Create(Instruction::Shl, inst.getOperand(0), shift);
        Instruction *newshli = dyn_cast<Instruction>(shli);
        newshli->insertAfter(&inst);
        unsigned int restVal = C->getValue().getSExtValue() - (2 << shiftVal);
        ConstantInt *rest = ConstantInt::get(C->getType(), restVal);
        Value* subi = BinaryOperator::Create(BinaryOperator::Sub, inst.getOperand(1), rest);
        newinst = dyn_cast<Instruction>(subi);
        newinst->insertAfter(newshli);
        break;

      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
        ConstantInt *shift =
          ConstantInt::get(C->getType(), shiftVal);
        newinst = BinaryOperator::Create(Instruction::LShr, inst.getOperand(0), shift);
        newinst->insertAfter(newshli);
        break;
  }

  return newinst;
}

/** @brief Check if the divisor is an integer constant and, it that case if it is a power of 2.
 * It implicitly check if the instruction is a division.
 * 
 * @param inst instruction to check
 * @return true if the divisor is a ConstantInt and a Power of 2, false otherwise.
*/
bool isDivisorPow2 (Instruction *inst)
{
  if (inst->getOpcode() != (BinaryOperator::UDiv || BinaryOperator::SDiv))
    return false;

  ConstantInt *d = dyn_cast<ConstantInt>(inst->getOperand(1));
  return (d && d->getValue().isPowerOf2());
}

bool runOnBasicBlock(BasicBlock &B) {
  for (auto &inst : B) 
  {
    // check for binary operations
    if (!inst.isBinaryOp())
      continue;

    std::pair<ConstantInt*, ConstantInt*> operands = getConstantInt(inst.getOperand(0), inst.getOperand(1));
    if (!operands.first && !operands.second)
      continue;

    /* Optimized instruction.
    * The Value type is necessary in order to include also the Argument objects (representig
    * function's arguments).
    */
    Value *i = getAlgebraicIdentity(operands, inst);
    if (!i)
      i = getStrengthReductionLeft(operands.first, inst);
    if (!i)
      i = getStrengthReductionRight(operands.second, inst);

      
    /*
    else if (inst.getOpcode() == BinaryOperator::Mul && operands.first->getValue().isPowerOf2()) 
    {
      // create shift constant
      ConstantInt *shift =
          ConstantInt::get(operands.first->getType(), operands.first->getValue().logBase2());
      // create a new instruction shl instruction
      i = BinaryOperator::Create(BinaryOperator::Shl, operands.second, shift);
      // isert the new shift instruction after the considered mul instruction
      Instruction *newinst = dyn_cast<Instruction>(i);
      newinst->insertAfter(&inst);
    } 
    */

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