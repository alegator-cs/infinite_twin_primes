import TwinPrimeExternal.Core

/-!
# Recursive MP/PM Certificate Model

This file formalizes the Lean-checkable core of Section 5 of the paper.

The C++ program still owns the finite search and recursive descent audit.  Lean
owns the certificate shape and the cardinality contradiction:

* there is a finite side-labeled actual MP/PM event set;
* there is a finite side-labeled predicted MP/PM event set;
* the generated arithmetic proves `actual.card < predicted.card`;
* the external finite routing audit says a cofinal exceptional tail realizes
  every predicted event as an actual event;
* `Finset.card_le_card` then contradicts the strict count inequality.

The file also records the two row identities that explain why the C++ search
uses split primes, i.e. primes for which `5` is a quadratic residue, plus the
side-event encoding and the decreasing-edge convention for descended primes.
-/

namespace TwinPrimeExternal

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

/--
Lean-side shape of the recursive MP/PM event certificate.

The events are already encoded as natural numbers by the generator:
`2*u` and `2*u+1` are the two side labels attached to a target-block midpoint
coordinate `u`.
-/
structure RecursiveMPPMEventCertificate where
  actualEvents : Finset Nat
  predictedEvents : Finset Nat
  actual_card : actualEvents.card = generatedMPPMCard
  predicted_card : predictedEvents.card = predictedEventCount
  predicted_realized_of_cofinalTail :
    (exists B, CofinalExceptionTail MidpointExceptionalPrime B) ->
      predictedEvents ⊆ actualEvents

namespace RecursiveMPPMEventCertificate

theorem predicted_card_exceeds_actual
    (cert : RecursiveMPPMEventCertificate) :
    cert.actualEvents.card < cert.predictedEvents.card := by
  rw [cert.actual_card, cert.predicted_card]
  exact predictedEventCount_exceeds_generatedMPPMCard

theorem false_of_cofinalTail
    (cert : RecursiveMPPMEventCertificate)
    (tail : exists B, CofinalExceptionTail MidpointExceptionalPrime B) :
    False := by
  have hsubset : cert.predictedEvents ⊆ cert.actualEvents :=
    cert.predicted_realized_of_cofinalTail tail
  have hle : cert.predictedEvents.card <= cert.actualEvents.card :=
    Finset.card_le_card hsubset
  have hgt : cert.actualEvents.card < cert.predictedEvents.card :=
    cert.predicted_card_exceeds_actual
  omega

end RecursiveMPPMEventCertificate

theorem no_cofinalExceptionTail_of_recursiveMPPMEventCertificate
    (cert : RecursiveMPPMEventCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  intro tail
  exact cert.false_of_cofinalTail tail

end TwinPrimeExternal
