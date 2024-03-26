// NOTE: Assertions have been autogenerated by utils/update_cc_test_checks.py UTC_ARGS: --filter "^define |tail call"
// RUN: %clang_cc1 -triple loongarch64 -emit-llvm -O2 %s -o - | FileCheck %s

typedef signed char v16i8 __attribute__((vector_size(16), aligned(16)));

// CHECK-LABEL: @test_vr0(
// CHECK:    tail call void asm sideeffect "", "{$vr0}"(<16 x i8> undef) #[[ATTR1:[0-9]+]], !srcloc !2
//
void test_vr0() {
    register v16i8 a asm ("$vr0");
    asm ("" :: "f"(a));
}

// CHECK-LABEL: @test_vr7(
// CHECK:    tail call void asm sideeffect "", "{$vr7}"(<16 x i8> undef) #[[ATTR1]], !srcloc !3
//
void test_vr7() {
    register v16i8 a asm ("$vr7");
    asm ("" :: "f"(a));
}

// CHECK-LABEL: @test_vr15(
// CHECK:    tail call void asm sideeffect "", "{$vr15}"(<16 x i8> undef) #[[ATTR1]], !srcloc !4
//
void test_vr15() {
    register v16i8 a asm ("$vr15");
    asm ("" :: "f"(a));
}

// CHECK-LABEL: @test_vr31(
// CHECK:    tail call void asm sideeffect "", "{$vr31}"(<16 x i8> undef) #[[ATTR1]], !srcloc !5
//
void test_vr31() {
    register v16i8 a asm ("$vr31");
    asm ("" :: "f"(a));
}