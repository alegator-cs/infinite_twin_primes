import TwinPrimeCertificate.Final
import TwinPrimeCertificate.RoutedMPPMChainBridge

/-!
# Generated Tail-Induction Certificate Wiring

This file connects the generated MP/PM overflow certificates to the final
tail-induction endpoint.

The canonical generated certificate surface is `RoutedChainRealizationCertificate`.
Its shards verify explicit arithmetic descent witnesses.  The realization
certificate then gives `¬ ∃ B, CofinalExceptionTail MidpointExceptionalPrime B`,
and Lean converts that no-tail theorem into the `MidpointTailInductionCertificate`
interface used by `Final.lean`.
-/

namespace TwinPrimeCertificate.GeneratedTailInductionCertificate

def fromRoutedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_routedMPPMChainCertificate cert)

theorem no_cofinalExceptionTail_of_routedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromRoutedChainRealization cert)

theorem arbitrarily_large_twins_of_routedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromRoutedChainRealization cert)

end TwinPrimeCertificate.GeneratedTailInductionCertificate

