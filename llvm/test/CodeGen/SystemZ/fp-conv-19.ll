; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py

; Test f128 to i128 bitcasts.
;
; RUN: llc < %s -mtriple=s390x-linux-gnu -mcpu=z10 \
; RUN:   | FileCheck -check-prefix=Z10 %s
;
; RUN: llc < %s -mtriple=s390x-linux-gnu -mcpu=z14 \
; RUN:   | FileCheck -check-prefix=Z14 %s

define i64 @extract_float_hi(ptr %0, ptr %1) {
; Z10-LABEL: extract_float_hi:
; Z10:       # %bb.0: # %entry
; Z10-NEXT:    ld %f0, 0(%r2)
; Z10-NEXT:    ld %f2, 8(%r2)
; Z10-NEXT:    ld %f1, 0(%r3)
; Z10-NEXT:    ld %f3, 8(%r3)
; Z10-NEXT:    axbr %f1, %f0
; Z10-NEXT:    lgdr %r2, %f1
; Z10-NEXT:    br %r14
;
; Z14-LABEL: extract_float_hi:
; Z14:       # %bb.0: # %entry
; Z14-NEXT:    vl %v0, 0(%r2), 3
; Z14-NEXT:    vl %v1, 0(%r3), 3
; Z14-NEXT:    wfaxb %v0, %v0, %v1
; Z14-NEXT:    vlgvg %r2, %v0, 0
; Z14-NEXT:    br %r14
entry:
  %x = load fp128, ptr %0
  %y = load fp128, ptr %1
  %add = fadd fp128 %x, %y
  %2 = bitcast fp128 %add to i128
  %u.sroa.0.0.extract.shift = lshr i128 %2, 64
  %u.sroa.0.0.extract.trunc = trunc i128 %u.sroa.0.0.extract.shift to i64
  ret i64 %u.sroa.0.0.extract.trunc
}

define i64 @extract_float_lo(ptr %0, ptr %1) {
; Z10-LABEL: extract_float_lo:
; Z10:       # %bb.0: # %entry
; Z10-NEXT:    ld %f0, 0(%r2)
; Z10-NEXT:    ld %f2, 8(%r2)
; Z10-NEXT:    ld %f1, 0(%r3)
; Z10-NEXT:    ld %f3, 8(%r3)
; Z10-NEXT:    axbr %f1, %f0
; Z10-NEXT:    lgdr %r2, %f3
; Z10-NEXT:    br %r14
;
; Z14-LABEL: extract_float_lo:
; Z14:       # %bb.0: # %entry
; Z14-NEXT:    vl %v0, 0(%r2), 3
; Z14-NEXT:    vl %v1, 0(%r3), 3
; Z14-NEXT:    wfaxb %v0, %v0, %v1
; Z14-NEXT:    vlgvg %r2, %v0, 1
; Z14-NEXT:    br %r14
entry:
  %x = load fp128, ptr %0
  %y = load fp128, ptr %1
  %add = fadd fp128 %x, %y
  %2 = bitcast fp128 %add to i128
  %u.sroa.0.0.extract.trunc = trunc i128 %2 to i64
  ret i64 %u.sroa.0.0.extract.trunc
}

define i128 @bitcast_128(ptr %0, ptr %1) {
; Z10-LABEL: bitcast_128:
; Z10:       # %bb.0: # %entry
; Z10-NEXT:    ld %f0, 0(%r3)
; Z10-NEXT:    ld %f2, 8(%r3)
; Z10-NEXT:    ld %f1, 0(%r4)
; Z10-NEXT:    ld %f3, 8(%r4)
; Z10-NEXT:    axbr %f1, %f0
; Z10-NEXT:    lgdr %r0, %f3
; Z10-NEXT:    lgdr %r1, %f1
; Z10-NEXT:    oill %r1, 1
; Z10-NEXT:    oill %r0, 3
; Z10-NEXT:    stg %r0, 8(%r2)
; Z10-NEXT:    stg %r1, 0(%r2)
; Z10-NEXT:    br %r14
;
; Z14-LABEL: bitcast_128:
; Z14:       # %bb.0: # %entry
; Z14-NEXT:    vl %v0, 0(%r3), 3
; Z14-NEXT:    vl %v1, 0(%r4), 3
; Z14-NEXT:    wfaxb %v0, %v0, %v1
; Z14-NEXT:    vlgvg %r0, %v0, 1
; Z14-NEXT:    vlgvg %r1, %v0, 0
; Z14-NEXT:    oill %r1, 1
; Z14-NEXT:    oill %r0, 3
; Z14-NEXT:    stg %r0, 8(%r2)
; Z14-NEXT:    stg %r1, 0(%r2)
; Z14-NEXT:    br %r14
entry:
  %x = load fp128, ptr %0
  %y = load fp128, ptr %1
  %add = fadd fp128 %x, %y
  %i = bitcast fp128 %add to i128
  %hibit = shl i128 1, 64
  %i2 = or i128 %i, %hibit
  %i3 = or i128 %i2, 3
  ret i128 %i3
}