import TwinPrimeExternal.GeneratedFixedGapCertificates

/-!
# Generated Fixed-Gap Recursive Certificates

Generated from `tools/search_fixed_gap_recursive_prefix_threshold.cpp`.

This file has the same trust-boundary shape as the twin-prime endpoint:
Lean checks the displayed cardinal arithmetic, while the C++ recursive
route-realization audit is represented by one external no-tail declaration per
fixed gap.
-/

namespace TwinPrimeExternal.GeneratedFixedGapRecursiveCertificates

namespace gap12

def d : Nat := 6
def actualGap : Nat := 12
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 164023
def actualSideEvents : Nat := 119574
def predictedUniverse : Nat := 328046
def predictedEvents : Nat := 123954
def falsePredictedEvents : Nat := 78737

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap12.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap12

namespace gap48

def d : Nat := 24
def actualGap : Nat := 48
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 124506
def actualSideEvents : Nat := 91376
def predictedUniverse : Nat := 249012
def predictedEvents : Nat := 104374
def falsePredictedEvents : Nat := 66178

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap48.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap48

namespace gap60

def d : Nat := 30
def actualGap : Nat := 60
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 334220
def actualSideEvents : Nat := 243660
def predictedUniverse : Nat := 668440
def predictedEvents : Nat := 274046
def falsePredictedEvents : Nat := 174099

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap60.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap60

namespace gap108

def d : Nat := 54
def actualGap : Nat := 108
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 328130
def actualSideEvents : Nat := 239454
def predictedUniverse : Nat := 656260
def predictedEvents : Nat := 245794
def falsePredictedEvents : Nat := 155876

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap108.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap108

namespace gap120

def d : Nat := 60
def actualGap : Nat := 120
def orientation : Nat := 1
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 142412
def actualSideEvents : Nat := 103979
def predictedUniverse : Nat := 284824
def predictedEvents : Nat := 115786
def falsePredictedEvents : Nat := 73496

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap120.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap120

namespace gap168

def d : Nat := 84
def actualGap : Nat := 168
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191297
def firstOverflowSpan : Nat := 33
def primeRoots : Nat := 2
def routedRoots : Nat := 2
def base : Nat := 359048
def actualSideEvents : Nat := 262304
def predictedUniverse : Nat := 718096
def predictedEvents : Nat := 287418
def falsePredictedEvents : Nat := 182271

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap168.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap168

namespace gap192

def d : Nat := 96
def actualGap : Nat := 192
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 124866
def actualSideEvents : Nat := 91546
def predictedUniverse : Nat := 249732
def predictedEvents : Nat := 101134
def falsePredictedEvents : Nat := 64095

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap192.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap192

namespace gap240

def d : Nat := 120
def actualGap : Nat := 240
def orientation : Nat := 0
def firstOverflowRoot : Nat := 191281
def firstOverflowSpan : Nat := 17
def primeRoots : Nat := 1
def routedRoots : Nat := 1
def base : Nat := 254210
def actualSideEvents : Nat := 186218
def predictedUniverse : Nat := 508420
def predictedEvents : Nat := 246566
def falsePredictedEvents : Nat := 156009

theorem predictedEvents_exceeds_actualSideEvents :
    actualSideEvents < predictedEvents := by
  norm_num [actualSideEvents, predictedEvents]

axiom external_no_cofinalExceptionTail :
    Not (exists K,
      TwinPrimeExternal.CofinalExceptionTail
        (TwinPrimeExternal.FixedGapExceptionalPrime d) K)

theorem arbitrarily_large_pairs :
    TwinPrimeExternal.ArbitrarilyLargeFixedGapPrimePairs d :=
  TwinPrimeExternal.GeneratedFixedGapCertificates.gap240.arbitrarily_large_pairs_of_no_tail
    external_no_cofinalExceptionTail

end gap240

end TwinPrimeExternal.GeneratedFixedGapRecursiveCertificates
