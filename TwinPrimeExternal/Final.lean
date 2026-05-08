import TwinPrimeExternal.RoutedMPPMChainBridge

/-!
# Final External-Certificate Endpoint

The theorem `arbitrarily_large_twins` is conditional only on the semantic
route-realization declaration named
`external_routedChains_realized_of_cofinalTail`.  The generated MP/PM overflow
is checked by Lean from explicit recursive descent chain shards.
-/

namespace TwinPrimeExternal

theorem no_cofinalExceptionTail :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_routedMPPMChainCertificate

theorem not_boundedTwinMids : Not BoundedTwinMids :=
  no_boundedTwinMids_of_no_cofinalExceptionTail no_cofinalExceptionTail

theorem arbitrarily_large_twins : ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    no_cofinalExceptionTail

end TwinPrimeExternal
