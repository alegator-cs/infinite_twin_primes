import TwinPrimeExternal.Core

/-!
# Tail-Induction Certificate Interface

This file is the assumption-free Lean wiring for the shifted-tail argument.

The mathematical/certificate content is packaged as a value of
`TailInductionCertificate Exception`.  Such a value has two parts:

* a base threshold whose cofinal exceptional tail is contradictory;
* a successor inheritance theorem saying that if tails starting after `B` are
  contradictory, then tails starting after `B + 1` are also contradictory.

From those two checked fields, Lean proves that no cofinal exceptional tail
exists at any threshold.  The twin-prime endpoint then follows from the core
finite-twins-to-cofinal-tail theorem in `Core.lean`.
-/

namespace TwinPrimeExternal

structure TailInductionCertificate (Exception : Nat -> Prop) where
  baseThreshold : Nat
  base_contradiction :
    CofinalTailContradicts Exception baseThreshold
  successor_contradiction :
    forall B,
      baseThreshold <= B ->
        CofinalTailContradicts Exception B ->
          CofinalTailContradicts Exception (B + 1)

namespace TailInductionCertificate

def of_no_cofinalTail
    {Exception : Nat -> Prop}
    (baseThreshold : Nat)
    (hno : Not (exists B, CofinalExceptionTail Exception B)) :
    TailInductionCertificate Exception where
  baseThreshold := baseThreshold
  base_contradiction := by
    intro tail
    exact hno ⟨baseThreshold, tail⟩
  successor_contradiction := by
    intro B _hB _hContradicts tail
    exact hno ⟨B + 1, tail⟩

theorem no_cofinalTail
    {Exception : Nat -> Prop}
    (cert : TailInductionCertificate Exception) :
    Not (exists B, CofinalExceptionTail Exception B) :=
  no_cofinalTail_of_base_and_successor_contradiction
    cert.base_contradiction cert.successor_contradiction

end TailInductionCertificate

abbrev MidpointTailInductionCertificate :=
  TailInductionCertificate MidpointExceptionalPrime

theorem no_cofinalExceptionTail_of_tailInductionCertificate
    (cert : MidpointTailInductionCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  cert.no_cofinalTail

theorem arbitrarily_large_twins_of_tailInductionCertificate
    (cert : MidpointTailInductionCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_tailInductionCertificate cert)

end TwinPrimeExternal
