import TwinPrimeExternal.Final
import TwinPrimeExternal.RoutedMPPMChainBridge

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

namespace TwinPrimeExternal.GeneratedTailInductionCertificate

def fromRoutedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeExternal.no_cofinalExceptionTail_of_routedMPPMChainCertificate cert)

theorem no_cofinalExceptionTail_of_routedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeExternal.no_cofinalExceptionTail
    (fromRoutedChainRealization cert)

theorem arbitrarily_large_twins_of_routedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeExternal.arbitrarily_large_twins
    (fromRoutedChainRealization cert)

end TwinPrimeExternal.GeneratedTailInductionCertificate
