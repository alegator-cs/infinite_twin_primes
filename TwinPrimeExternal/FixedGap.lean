import TwinPrimeExternal.Core

/-!
# Fixed-Gap Endpoint Skeleton

This file factors the midpoint-row endpoint through an arbitrary fixed
half-gap `d`.  The original twin-prime endpoint is the case `d = 1`.

The reusable Lean theorem is intentionally modest:

* if a C++/finite certificate rules out a cofinal tail of fixed-gap
  midpoint-exceptional primes for a chosen `d`;
* then prime pairs `p, p + 2*d` occur arbitrarily far out.

The file also records the most algebraically friendly small gaps up to actual
gap `246`: those whose quadratic routing identity comes from a Pythagorean
factor pair `A * B = 2*d`, `A^2 + B^2 = C^2`.
-/

namespace TwinPrimeExternal

/-- A prime pair of fixed gap `2*d`, centered at `r*h`. -/
def FixedGapMidpointWitnessAt (d r h : Nat) : Prop :=
  Nat.Prime (r * h - d) /\ Nat.Prime (r * h + d)

/-- `r` is exceptional for the fixed half-gap `d` if its midpoint row has no pair. -/
def FixedGapExceptionalPrime (d r : Nat) : Prop :=
  Nat.Prime r /\
    forall h, MidpointRowIndex r h -> Not (FixedGapMidpointWitnessAt d r h)

/-- Bounded fixed-gap midpoints. -/
def BoundedFixedGapMids (d : Nat) : Prop :=
  exists M,
    forall m, M < m ->
      Not (Nat.Prime (m - d) /\ Nat.Prime (m + d))

/-- Prime pairs of gap `2*d` occur arbitrarily far out. -/
def ArbitrarilyLargeFixedGapPrimePairs (d : Nat) : Prop :=
  forall N, exists p, N <= p /\ Nat.Prime p /\ Nat.Prime (p + 2 * d)

/--
Bounded fixed-gap midpoints force a cofinal tail of fixed-gap exceptional
primes.
-/
theorem boundedFixedGapMids_forces_cofinalTail_fixedGapExceptionalPrime
    {d : Nat}
    (hbounded : BoundedFixedGapMids d) :
    exists B, CofinalExceptionTail (FixedGapExceptionalPrime d) B := by
  rcases hbounded with ⟨M, hnoPairsAbove⟩
  refine ⟨M, ?_⟩
  intro r hr hMr
  constructor
  · exact hr
  · intro h hidx hpair
    have hr_le_center : r <= r * h := by
      calc
        r = r * 1 := by rw [Nat.mul_one]
        _ <= r * h := Nat.mul_le_mul_left r hidx.1
    have hM_center : M < r * h :=
      lt_of_lt_of_le hMr hr_le_center
    exact hnoPairsAbove (r * h) hM_center hpair

theorem arbitrarily_large_fixedGapPairs_of_not_boundedFixedGapMids
    {d : Nat}
    (hnotBounded : Not (BoundedFixedGapMids d)) :
    ArbitrarilyLargeFixedGapPrimePairs d := by
  intro N
  by_contra hnone
  apply hnotBounded
  refine ⟨N + d + 1, ?_⟩
  intro m hm hpair
  apply hnone
  refine ⟨m - d, ?_, ?_, ?_⟩
  · omega
  · exact hpair.1
  · have hshift : m - d + 2 * d = m + d := by
      have htwo : 2 <= m - d := hpair.1.two_le
      omega
    simpa [hshift] using hpair.2

theorem no_boundedFixedGapMids_of_no_cofinalFixedGapExceptionTail
    {d : Nat}
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime d) B)) :
    Not (BoundedFixedGapMids d) := by
  intro hbounded
  exact hno
    (boundedFixedGapMids_forces_cofinalTail_fixedGapExceptionalPrime hbounded)

/--
Reusable fixed-gap endpoint: a no-cofinal-exception-tail certificate for
half-gap `d` proves arbitrarily large prime pairs separated by `2*d`.
-/
theorem arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail
    {d : Nat}
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime d) B)) :
    ArbitrarilyLargeFixedGapPrimePairs d :=
  arbitrarily_large_fixedGapPairs_of_not_boundedFixedGapMids
    (no_boundedFixedGapMids_of_no_cofinalFixedGapExceptionTail hno)

/--
Quadratic fixed-gap routing identity.

If `A * B = 2*d`, then the midpoint
`u * (u + A + B) + d` has neighbor factorizations

* `X - d = u * (u + A + B)`;
* `X + d = (u + A) * (u + B)`.
-/
structure FixedGapQuadraticFamily (d : Nat) where
  A : Nat
  B : Nat
  C : Nat
  product_eq : A * B = 2 * d
  pythagorean : A ^ 2 + B ^ 2 = C ^ 2

namespace FixedGapQuadraticFamily

theorem left_neighbor_eq
    {d u : Nat}
    (family : FixedGapQuadraticFamily d) :
    (u * (u + family.A + family.B) + d) - d =
      u * (u + family.A + family.B) := by
  omega

theorem right_neighbor_eq
    {d u : Nat}
    (family : FixedGapQuadraticFamily d) :
    (u * (u + family.A + family.B) + d) + d =
      (u + family.A) * (u + family.B) := by
  have hprod : family.A * family.B = 2 * d := family.product_eq
  nlinarith

end FixedGapQuadraticFamily

/-!
## Small Pythagorean fixed-gap candidates

These are the actual gaps `2*d <= 246` whose routing identity has square
discriminant.  They are the first targets that look genuinely reusable for a
Polignac-adjacent certificate pass.
-/

def fixedGapFamily_d6 : FixedGapQuadraticFamily 6 where
  A := 3
  B := 4
  C := 5
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d24 : FixedGapQuadraticFamily 24 where
  A := 6
  B := 8
  C := 10
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d30 : FixedGapQuadraticFamily 30 where
  A := 5
  B := 12
  C := 13
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d54 : FixedGapQuadraticFamily 54 where
  A := 9
  B := 12
  C := 15
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d60 : FixedGapQuadraticFamily 60 where
  A := 8
  B := 15
  C := 17
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d84 : FixedGapQuadraticFamily 84 where
  A := 7
  B := 24
  C := 25
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d96 : FixedGapQuadraticFamily 96 where
  A := 12
  B := 16
  C := 20
  product_eq := by norm_num
  pythagorean := by norm_num

def fixedGapFamily_d120 : FixedGapQuadraticFamily 120 where
  A := 10
  B := 24
  C := 26
  product_eq := by norm_num
  pythagorean := by norm_num

/--
The current hand-selected list of Pythagorean fixed half-gaps with actual gap
at most `246`.
-/
def pythagoreanFixedHalfGapsUpTo246 : List Nat :=
  [6, 24, 30, 54, 60, 84, 96, 120]

def pythagoreanFixedActualGapsUpTo246 : List Nat :=
  pythagoreanFixedHalfGapsUpTo246.map (fun d => 2 * d)

theorem pythagoreanFixedActualGapsUpTo246_eq :
    pythagoreanFixedActualGapsUpTo246 =
      [12, 48, 60, 108, 120, 168, 192, 240] := by
  rfl

/--
Representative endpoint for gap `12`, conditional only on the corresponding
external no-tail certificate.
-/
theorem arbitrarily_large_gap12_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 6) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 6 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap48_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 24) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 24 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap60_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 30) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 30 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap108_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 54) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 54 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap120_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 60) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 60 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap168_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 84) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 84 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

theorem arbitrarily_large_gap192_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 96) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 96 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

/--
Endpoint for gap `240`, the largest Pythagorean candidate below the `246`
bounded-gap threshold.
-/
theorem arbitrarily_large_gap240_pairs_of_no_tail
    (hno :
      Not (exists B,
        CofinalExceptionTail (FixedGapExceptionalPrime 120) B)) :
    ArbitrarilyLargeFixedGapPrimePairs 120 :=
  arbitrarily_large_fixedGapPairs_of_no_cofinalExceptionTail hno

end TwinPrimeExternal
