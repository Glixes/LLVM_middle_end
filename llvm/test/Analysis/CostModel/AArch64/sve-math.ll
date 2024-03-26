; NOTE: Assertions have been autogenerated by utils/update_analyze_test_checks.py
; RUN: opt -mtriple=aarch64-- -mattr=+sve -passes="print<cost-model>" 2>&1 -disable-output -cost-kind=throughput   < %s | FileCheck %s --check-prefix=THRU
; RUN: opt -mtriple=aarch64-- -mattr=+sve -passes="print<cost-model>" 2>&1 -disable-output -cost-kind=latency      < %s | FileCheck %s --check-prefix=LATE
; RUN: opt -mtriple=aarch64-- -mattr=+sve -passes="print<cost-model>" 2>&1 -disable-output -cost-kind=code-size    < %s | FileCheck %s --check-prefix=SIZE
; RUN: opt -mtriple=aarch64-- -mattr=+sve -passes="print<cost-model>" 2>&1 -disable-output -cost-kind=size-latency < %s | FileCheck %s --check-prefix=SIZE_LATE

target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"

declare <vscale x 2 x double> @llvm.sqrt.v2f64(<vscale x 2 x double>)

define <vscale x 2 x double> @fadd_v2f64(<vscale x 2 x double> %a, <vscale x 2 x double> %b) {
; THRU-LABEL: 'fadd_v2f64'
; THRU-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: %r = fadd <vscale x 2 x double> %a, %b
; THRU-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: ret <vscale x 2 x double> %r
;
; LATE-LABEL: 'fadd_v2f64'
; LATE-NEXT:  Cost Model: Found an estimated cost of 3 for instruction: %r = fadd <vscale x 2 x double> %a, %b
; LATE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
; SIZE-LABEL: 'fadd_v2f64'
; SIZE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: %r = fadd <vscale x 2 x double> %a, %b
; SIZE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
; SIZE_LATE-LABEL: 'fadd_v2f64'
; SIZE_LATE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: %r = fadd <vscale x 2 x double> %a, %b
; SIZE_LATE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
  %r = fadd <vscale x 2 x double> %a, %b
  ret <vscale x 2 x double> %r
}

define <vscale x 2 x double> @sqrt_v2f64(<vscale x 2 x double> %a) {
; THRU-LABEL: 'sqrt_v2f64'
; THRU-NEXT:  Cost Model: Found an estimated cost of 2 for instruction: %r = call <vscale x 2 x double> @llvm.sqrt.nxv2f64(<vscale x 2 x double> %a)
; THRU-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: ret <vscale x 2 x double> %r
;
; LATE-LABEL: 'sqrt_v2f64'
; LATE-NEXT:  Cost Model: Found an estimated cost of 2 for instruction: %r = call <vscale x 2 x double> @llvm.sqrt.nxv2f64(<vscale x 2 x double> %a)
; LATE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
; SIZE-LABEL: 'sqrt_v2f64'
; SIZE-NEXT:  Cost Model: Found an estimated cost of 2 for instruction: %r = call <vscale x 2 x double> @llvm.sqrt.nxv2f64(<vscale x 2 x double> %a)
; SIZE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
; SIZE_LATE-LABEL: 'sqrt_v2f64'
; SIZE_LATE-NEXT:  Cost Model: Found an estimated cost of 2 for instruction: %r = call <vscale x 2 x double> @llvm.sqrt.nxv2f64(<vscale x 2 x double> %a)
; SIZE_LATE-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <vscale x 2 x double> %r
;
  %r = call <vscale x 2 x double> @llvm.sqrt.v2f64(<vscale x 2 x double> %a)
  ret <vscale x 2 x double> %r
}