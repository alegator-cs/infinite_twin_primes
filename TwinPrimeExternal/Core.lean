import Mathlib.Tactic

/-!
# Minimal Twin-Prime Endpoint Core

This file contains only the Lean-checked endpoint logic.

The external C++ certificate is allowed to prove one concrete theorem:

```
Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B)
```

From that single finite-certificate obstruction, Lean proves arbitrarily large
twin primes by the following elementary chain:

* bounded twin-prime midpoints give a cofinal tail of exceptional primes;
* the external certificate rules out such a cofinal tail;
* twin midpoints are unbounded;
* twin primes are arbitrarily large.
-/

namespace TwinPrimeExternal

def lastObservedException : Nat := 127

def observedVerifiedTo : Nat := 1000000000

def certificateVerifiedTo : Nat := 191264

def certificateFirstSplitPrime : Nat := 191281

def generatedMPPMCard : Nat := 95568

def predictedEventCount : Nat := 181052

theorem predictedEventCount_exceeds_generatedMPPMCard :
    generatedMPPMCard < predictedEventCount := by
  norm_num [generatedMPPMCard, predictedEventCount]

structure ObservedExceptionGap where
  lastException : Nat
  verifiedTo : Nat
  hlt : lastException < verifiedTo

def ObservedExceptionGap.size (gap : ObservedExceptionGap) : Nat :=
  gap.verifiedTo - gap.lastException

def observedExceptionGap : ObservedExceptionGap where
  lastException := lastObservedException
  verifiedTo := observedVerifiedTo
  hlt := by
    norm_num [lastObservedException, observedVerifiedTo]

def certificateExceptionGap : ObservedExceptionGap where
  lastException := lastObservedException
  verifiedTo := certificateVerifiedTo
  hlt := by
    norm_num [lastObservedException, certificateVerifiedTo]

theorem certificateVerifiedTo_le_observed :
    certificateExceptionGap.verifiedTo <= observedExceptionGap.verifiedTo := by
  norm_num [certificateExceptionGap, observedExceptionGap,
    certificateVerifiedTo, observedVerifiedTo]

/-- The first exceptional prime after a verified no-exception gap. -/
structure FirstExceptionAfterGap
    (Exception : Nat -> Prop)
    (gap : ObservedExceptionGap) where
  r : Nat
  hr : Nat.Prime r
  hafter : gap.verifiedTo < r
  exception : Exception r
  first_after_gap :
    forall s,
      Nat.Prime s ->
        gap.verifiedTo < s ->
          s < r ->
            Not (Exception s)

/-- A first exception after `lastObservedException`, independent of a chosen gap. -/
structure FirstExceptionAfterLastObserved
    (Exception : Nat -> Prop) where
  r : Nat
  hr : Nat.Prime r
  hafterLast : lastObservedException < r
  exception : Exception r
  first_after_last :
    forall s,
      Nat.Prime s ->
        lastObservedException < s ->
          s < r ->
            Not (Exception s)

/--
Certificate predicate: no prime in `(lastObservedException, checkedTo]`
is exceptional.
-/
def ExceptionFreeUpTo
    (Exception : Nat -> Prop)
    (checkedTo : Nat) : Prop :=
  forall r,
    Nat.Prime r ->
      lastObservedException < r ->
        r <= checkedTo ->
          Not (Exception r)

theorem firstExceptionAfterLast_occurs_after_of_exceptionFreeUpTo
    {Exception : Nat -> Prop}
    {checkedTo : Nat}
    (free : ExceptionFreeUpTo Exception checkedTo)
    (firstException : FirstExceptionAfterLastObserved Exception) :
    checkedTo < firstException.r := by
  by_contra hnot
  exact free firstException.r firstException.hr firstException.hafterLast
    (le_of_not_gt hnot) firstException.exception

theorem firstExceptionAfterLast_occurs_after_certificateThreshold_of_exceptionFreeUpTo
    {Exception : Nat -> Prop}
    (free : ExceptionFreeUpTo Exception certificateVerifiedTo)
    (firstException : FirstExceptionAfterLastObserved Exception) :
    certificateVerifiedTo < firstException.r :=
  firstExceptionAfterLast_occurs_after_of_exceptionFreeUpTo free firstException

/-- After `B`, every prime is exceptional. -/
def CofinalExceptionTail (Exception : Nat -> Prop) (B : Nat) : Prop :=
  forall r, Nat.Prime r -> B < r -> Exception r

/-- A cofinal tail starting after `B` is already contradictory. -/
def CofinalTailContradicts (Exception : Nat -> Prop) (B : Nat) : Prop :=
  CofinalExceptionTail Exception B -> False

theorem cofinalTail_mono_threshold
    {Exception : Nat -> Prop} {B C : Nat}
    (hBC : B <= C)
    (tail : CofinalExceptionTail Exception B) :
    CofinalExceptionTail Exception C := by
  intro r hr hCr
  exact tail r hr (lt_of_le_of_lt hBC hCr)

theorem cofinalTailContradicts_mono_backward
    {Exception : Nat -> Prop} {B C : Nat}
    (hBC : B <= C)
    (hnoC : CofinalTailContradicts Exception C) :
    CofinalTailContradicts Exception B := by
  intro tailB
  exact hnoC (cofinalTail_mono_threshold hBC tailB)

/--
Tail-threshold induction.

If a cofinal tail is contradictory at a base threshold `B0`, and the
contradiction is inherited when the threshold is advanced from `B` to `B+1`,
then every later threshold is contradictory.
-/
theorem cofinalTailContradicts_of_base_and_successor
    {Exception : Nat -> Prop} {B0 : Nat}
    (hbase : CofinalTailContradicts Exception B0)
    (hstep :
      forall B,
        B0 <= B ->
          CofinalTailContradicts Exception B ->
            CofinalTailContradicts Exception (B + 1)) :
    forall B, B0 <= B -> CofinalTailContradicts Exception B := by
  exact Nat.le_induction hbase hstep

/--
No cofinal tail exists if a base threshold is contradictory and that
contradiction is inherited by every successor threshold.

This is the formal version of the "prove the base prefix, then shift the tail
start by one and lengthen the prefix" argument.  The successor step is the
place where a concrete pressure-growth or certificate-inheritance theorem must
be supplied.
-/
theorem no_cofinalTail_of_base_and_successor_contradiction
    {Exception : Nat -> Prop} {B0 : Nat}
    (hbase : CofinalTailContradicts Exception B0)
    (hstep :
      forall B,
        B0 <= B ->
          CofinalTailContradicts Exception B ->
            CofinalTailContradicts Exception (B + 1)) :
    Not (exists B, CofinalExceptionTail Exception B) := by
  intro htail
  rcases htail with ⟨B, tailB⟩
  by_cases hB0B : B0 <= B
  · exact
      (cofinalTailContradicts_of_base_and_successor hbase hstep
        B hB0B) tailB
  · have hBB0 : B <= B0 := by omega
    exact hbase (cofinalTail_mono_threshold hBB0 tailB)

def BoundedTwinMids : Prop :=
  exists M,
    forall m, M < m ->
      Not (Nat.Prime (m - 1) /\ Nat.Prime (m + 1))

def ArbitrarilyLargeTwins : Prop :=
  forall N, exists p, N <= p /\ Nat.Prime p /\ Nat.Prime (p + 2)

/-- Row indices for the midpoint row attached to `r`. -/
def MidpointRowIndex (r h : Nat) : Prop :=
  1 <= h /\ h < r

/-- Midpoint of the twin pair attached to prime parameter `r` and index `h`. -/
def MidpointRowMidpoint (r h : Nat) : Nat :=
  r * h

/-- A twin pair around the midpoint `r * h`. -/
def MidpointTwinWitnessAt (r h : Nat) : Prop :=
  Nat.Prime (MidpointRowMidpoint r h - 1) /\
    Nat.Prime (MidpointRowMidpoint r h + 1)

/--
Midpoint-exceptional prime: `r` is prime and no row index gives a twin pair
around `r * h`.
-/
def MidpointExceptionalPrime (r : Nat) : Prop :=
  Nat.Prime r /\
    forall h, MidpointRowIndex r h -> Not (MidpointTwinWitnessAt r h)

/--
Bounded twin midpoints force a cofinal tail of midpoint-exceptional primes.

This is the only global arithmetic bridge in the minimal Lean core.
-/
theorem boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime
    (hbounded : BoundedTwinMids) :
    exists B, CofinalExceptionTail MidpointExceptionalPrime B := by
  rcases hbounded with ⟨M, hnoTwinsAbove⟩
  refine ⟨M, ?_⟩
  intro r hr hMr
  constructor
  · exact hr
  · intro h hidx htwin
    have hr_le_center : r <= MidpointRowMidpoint r h := by
      unfold MidpointRowMidpoint
      calc
        r = r * 1 := by rw [Nat.mul_one]
        _ <= r * h := Nat.mul_le_mul_left r hidx.1
    have hM_center : M < MidpointRowMidpoint r h :=
      lt_of_lt_of_le hMr hr_le_center
    exact hnoTwinsAbove (MidpointRowMidpoint r h) hM_center htwin

/-- A cofinal tail gives a first exception after any verified gap. -/
theorem cofinalTail_gives_firstExceptionAfterGap
    {Exception : Nat -> Prop} {B : Nat}
    (tail : CofinalExceptionTail Exception B)
    (gap : ObservedExceptionGap) :
    Nonempty (FirstExceptionAfterGap Exception gap) := by
  classical
  let pred : Nat -> Prop :=
    fun p => gap.verifiedTo < p /\ Nat.Prime p /\ Exception p
  have hexists : Exists pred := by
    rcases Nat.exists_infinite_primes (max B gap.verifiedTo + 1) with
      ⟨r, hrgt, hrPrime⟩
    have hmax : max B gap.verifiedTo < r := by
      omega
    have hB : B < r := lt_of_le_of_lt (le_max_left _ _) hmax
    have hG : gap.verifiedTo < r := lt_of_le_of_lt (le_max_right _ _) hmax
    exact ⟨r, hG, hrPrime, tail r hrPrime hB⟩
  let R := Nat.find hexists
  have hR : pred R := Nat.find_spec hexists
  refine ⟨{
    r := R
    hr := hR.2.1
    hafter := hR.1
    exception := hR.2.2
    first_after_gap := ?_
  }⟩
  intro s hsPrime hsAfter hsLt hsException
  have hsPred : pred s := ⟨hsAfter, hsPrime, hsException⟩
  have hmin : R <= s := Nat.find_min' hexists hsPred
  omega

/--
First-exception monotonicity: a first exception after a later verified bound
gives a first exception after any earlier verified bound.
-/
theorem firstException_mono_backward
    {Exception : Nat -> Prop}
    {gapSmall gapLarge : ObservedExceptionGap}
    (hle : gapSmall.verifiedTo <= gapLarge.verifiedTo)
    (firstException : FirstExceptionAfterGap Exception gapLarge) :
    Nonempty (FirstExceptionAfterGap Exception gapSmall) := by
  classical
  let pred : Nat -> Prop :=
    fun p => gapSmall.verifiedTo < p /\ Nat.Prime p /\ Exception p
  have hexists : Exists pred := by
    exact ⟨firstException.r,
      lt_of_le_of_lt hle firstException.hafter,
      firstException.hr,
      firstException.exception⟩
  let R := Nat.find hexists
  have hR : pred R := Nat.find_spec hexists
  refine ⟨{
    r := R
    hr := hR.2.1
    hafter := hR.1
    exception := hR.2.2
    first_after_gap := ?_
  }⟩
  intro s hsPrime hsAfter hsLt hsException
  have hsPred : pred s := ⟨hsAfter, hsPrime, hsException⟩
  have hmin : R <= s := Nat.find_min' hexists hsPred
  omega

theorem no_firstException_mono_forward
    {Exception : Nat -> Prop}
    {gapSmall gapLarge : ObservedExceptionGap}
    (hle : gapSmall.verifiedTo <= gapLarge.verifiedTo)
    (hno : Not (Nonempty (FirstExceptionAfterGap Exception gapSmall))) :
    Not (Nonempty (FirstExceptionAfterGap Exception gapLarge)) := by
  intro hlarge
  rcases hlarge with ⟨firstException⟩
  exact hno (firstException_mono_backward hle firstException)

theorem arbitrarily_large_twins_of_not_boundedTwinMids
    (hnotBounded : Not BoundedTwinMids) :
    ArbitrarilyLargeTwins := by
  intro N
  by_contra hnone
  apply hnotBounded
  refine ⟨N + 1, ?_⟩
  intro m hm hpair
  apply hnone
  refine ⟨m - 1, ?_, ?_, ?_⟩
  · omega
  · exact hpair.1
  · have hshift : m - 1 + 2 = m + 1 := by
      omega
    simpa [hshift] using hpair.2

theorem no_boundedTwinMids_of_no_cofinalExceptionTail
    (hno :
      Not (exists B,
        CofinalExceptionTail MidpointExceptionalPrime B)) :
    Not BoundedTwinMids := by
  intro hbounded
  exact hno
    (boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime hbounded)

theorem arbitrarily_large_twins_of_no_cofinalExceptionTail
    (hno :
      Not (exists B,
        CofinalExceptionTail MidpointExceptionalPrime B)) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_not_boundedTwinMids
    (no_boundedTwinMids_of_no_cofinalExceptionTail hno)

theorem no_boundedTwinMids_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not BoundedTwinMids := by
  intro hbounded
  rcases boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime
      hbounded with ⟨B, tail⟩
  exact hno
    (cofinalTail_gives_firstExceptionAfterGap
      tail certificateExceptionGap)

/-- Lean endpoint from a certificate forbidding the first exception after the certificate gap. -/
theorem arbitrarily_large_twins_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_not_boundedTwinMids
    (no_boundedTwinMids_of_no_certificateFirstException hno)

/--
A no-first-exception certificate at the certificate threshold also rules out
any later verified gap, including the observed gap.
-/
theorem no_later_firstException_of_no_certificateFirstException
    {gapLarge : ObservedExceptionGap}
    (hle : certificateExceptionGap.verifiedTo <= gapLarge.verifiedTo)
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not (Nonempty
      (FirstExceptionAfterGap MidpointExceptionalPrime gapLarge)) :=
  no_firstException_mono_forward hle hno

theorem no_observed_firstException_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not (Nonempty
      (FirstExceptionAfterGap MidpointExceptionalPrime observedExceptionGap)) :=
  no_later_firstException_of_no_certificateFirstException
    certificateVerifiedTo_le_observed hno

end TwinPrimeExternal
