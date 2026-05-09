import TwinPrimeCertificate.Final
import TwinPrimeCertificate.RoutedMPPMChainBridge

/-!
# Generated Tail-Induction Certificate Wiring

This file exposes the single public certificate endpoint.

The finite base case is the generated routed MP/PM overflow checked by the
sharded Lean certificate.  The only remaining proof input is successor
recovery: once tails beginning at `B` are contradictory, tails beginning at
`B + 1` are contradictory too.  The DFI/Toth-shaped multiplicity theorem in
`QuadraticRootSupply` is the intended route to that successor-recovery field.
-/

namespace TwinPrimeCertificate.GeneratedTailInductionCertificate

/--
Generated successor-recovery certificate.

The `base` field is the concrete generated overflow at
`certificateVerifiedTo`.  The `successor_recovery` field is the inductive step
for the tail threshold.
-/
structure GeneratedSuccessorRecoveryCertificate where
  base : TwinPrimeCertificate.RoutedBaseCaseRealizationCertificate
  successor_recovery :
    ∀ B,
      certificateVerifiedTo <= B ->
        CofinalTailContradicts MidpointExceptionalPrime B ->
          CofinalTailContradicts MidpointExceptionalPrime (B + 1)

def fromGeneratedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    MidpointTailInductionCertificate where
  baseThreshold := certificateVerifiedTo
  base_contradiction :=
    cofinalTailContradicts_certificateVerifiedTo_of_routedBaseCaseCertificate
      cert.base
  successor_contradiction := cert.successor_recovery

theorem no_cofinalExceptionTail_of_generatedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromGeneratedSuccessorRecovery cert)

theorem arbitrarily_large_twins_of_generatedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromGeneratedSuccessorRecovery cert)

end TwinPrimeCertificate.GeneratedTailInductionCertificate
