import TwinPrimeExternal.Final
import TwinPrimeExternal.GeneratedCertificate
import TwinPrimeExternal.RoutedMPPMChainBridge

/-!
# Generated Tail-Induction Certificate Wiring

This file connects the generated MP/PM overflow certificates to the final
tail-induction endpoint.

There are two available generated certificate surfaces:

* `GeneratedCertificate.GeneratedRouteRealization`, the count-only generated
  MP/PM overflow surface;
* `RoutedChainRealizationCertificate`, the Lean-checked routed-chain surface
  whose shards verify explicit arithmetic descent witnesses.

Either one gives `¬ ∃ B, CofinalExceptionTail MidpointExceptionalPrime B`.
Lean then converts that no-tail theorem into the `MidpointTailInductionCertificate`
interface used by `Final.lean`.
-/

namespace TwinPrimeExternal.GeneratedTailInductionCertificate

def fromGeneratedRouteRealization
    (realized : GeneratedCertificate.GeneratedRouteRealization) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (GeneratedCertificate.no_cofinalExceptionTail realized)

def fromRoutedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeExternal.no_cofinalExceptionTail_of_routedMPPMChainCertificate cert)

theorem no_cofinalExceptionTail_of_generatedRouteRealization
    (realized : GeneratedCertificate.GeneratedRouteRealization) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeExternal.no_cofinalExceptionTail
    (fromGeneratedRouteRealization realized)

theorem no_cofinalExceptionTail_of_routedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeExternal.no_cofinalExceptionTail
    (fromRoutedChainRealization cert)

theorem arbitrarily_large_twins_of_generatedRouteRealization
    (realized : GeneratedCertificate.GeneratedRouteRealization) :
    ArbitrarilyLargeTwins :=
  TwinPrimeExternal.arbitrarily_large_twins
    (fromGeneratedRouteRealization realized)

theorem arbitrarily_large_twins_of_routedChainRealization
    (cert : TwinPrimeExternal.RoutedChainRealizationCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeExternal.arbitrarily_large_twins
    (fromRoutedChainRealization cert)

end TwinPrimeExternal.GeneratedTailInductionCertificate
