import TwinPrimeCertificate.Core

/-!
# Recursive MP/PM Arithmetic Primitives

This file formalizes the Lean-checkable core of Section 5 of the paper.

It records the row identities that explain why the C++ search uses split
primes, i.e. primes for which `5` is a quadratic residue, plus the side-event
encoding and the decreasing-edge convention for descended primes.
-/

namespace TwinPrimeCertificate

/-- Left-row discriminant identity:
`p ∣ u(u+3)+1` forces `(2u+3)^2 ≡ 5 (mod p)` whenever `p` is odd. -/
theorem left_row_residue5_identity (u : Nat) :
    4 * (u * (u + 3) + 1) + 5 = (2 * u + 3) ^ 2 := by
  ring

/-- Right-row discriminant identity:
`p ∣ (u+1)(u+4)+1` forces `(2u+5)^2 ≡ 5 (mod p)` whenever `p` is odd. -/
theorem right_row_residue5_identity (u : Nat) :
    4 * ((u + 1) * (u + 4) + 1) + 5 = (2 * u + 5) ^ 2 := by
  ring

/--
`5` is a quadratic residue modulo `p`, represented without Legendre-symbol
machinery.
-/
def FiveQuadraticResidueModulo (p : Nat) : Prop :=
  Exists (fun x : Nat => Nat.ModEq p (x ^ 2) 5)

/--
A divisor of a left quadratic row is a split prime candidate: if
`p | u(u+3)+1`, then `(2u+3)^2 ≡ 5 (mod p)`.
-/
theorem left_row_divisor_gives_residue5
    {p u : Nat}
    (hdiv : Dvd.dvd p (u * (u + 3) + 1)) :
    FiveQuadraticResidueModulo p := by
  refine Exists.intro (2 * u + 3) ?_
  have hrow : Nat.ModEq p (u * (u + 3) + 1) 0 :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  have h4row : Nat.ModEq p (4 * (u * (u + 3) + 1)) (4 * 0) :=
    Nat.ModEq.mul (Nat.ModEq.refl 4) hrow
  have hplus :
      Nat.ModEq p (4 * (u * (u + 3) + 1) + 5) (4 * 0 + 5) :=
    Nat.ModEq.add h4row (Nat.ModEq.refl 5)
  simpa [left_row_residue5_identity u] using hplus

/--
A divisor of a right quadratic row is a split prime candidate: if
`p | (u+1)(u+4)+1`, then `(2u+5)^2 ≡ 5 (mod p)`.
-/
theorem right_row_divisor_gives_residue5
    {p u : Nat}
    (hdiv : Dvd.dvd p ((u + 1) * (u + 4) + 1)) :
    FiveQuadraticResidueModulo p := by
  refine Exists.intro (2 * u + 5) ?_
  have hrow : Nat.ModEq p ((u + 1) * (u + 4) + 1) 0 :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  have h4row :
      Nat.ModEq p (4 * ((u + 1) * (u + 4) + 1)) (4 * 0) :=
    Nat.ModEq.mul (Nat.ModEq.refl 4) hrow
  have hplus :
      Nat.ModEq p (4 * ((u + 1) * (u + 4) + 1) + 5) (4 * 0 + 5) :=
    Nat.ModEq.add h4row (Nat.ModEq.refl 5)
  simpa [right_row_residue5_identity u] using hplus

/-- Width-two left routing identity used by the recursive closure. -/
theorem quad_route_left_identity (u : Nat) :
    u * (u + 3) + 2 = (u + 1) * (u + 2) := by
  nlinarith

/-- Width-two right routing identity used by the recursive closure. -/
theorem quad_route_right_identity (u : Nat) :
    (u + 1) * (u + 4) + 2 = (u + 2) * (u + 3) := by
  nlinarith

/-- Encode a target-block coordinate and a side label as one natural number. -/
def encodeSideEvent (u side : Nat) : Nat :=
  2 * u + side

theorem encodeSideEvent_zero_ne_one (u : Nat) :
    encodeSideEvent u 0 ≠ encodeSideEvent u 1 := by
  unfold encodeSideEvent
  omega

theorem encodeSideEvent_injective_of_side_lt_two
    {u v side₁ side₂ : Nat}
    (hside₁ : side₁ < 2)
    (hside₂ : side₂ < 2)
    (henc : encodeSideEvent u side₁ = encodeSideEvent v side₂) :
    u = v ∧ side₁ = side₂ := by
  unfold encodeSideEvent at henc
  omega

/-- A descended prime edge is oriented from a parent prime to a smaller child. -/
def DescendedPrimeEdge (parent child : Nat) : Prop :=
  child < parent

theorem DescendedPrimeEdge.decreases
    {parent child : Nat}
    (edge : DescendedPrimeEdge parent child) :
    child < parent :=
  edge

theorem DescendedPrimeEdge.irrefl (p : Nat) :
    Not (DescendedPrimeEdge p p) := by
  intro h
  exact Nat.lt_irrefl p h

theorem DescendedPrimeEdge.no_two_cycle
    {p q : Nat}
    (hpq : DescendedPrimeEdge p q)
    (hqp : DescendedPrimeEdge q p) :
    False := by
  unfold DescendedPrimeEdge at hpq hqp
  omega

end TwinPrimeCertificate

