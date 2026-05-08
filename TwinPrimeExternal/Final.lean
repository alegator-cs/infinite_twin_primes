import TwinPrimeExternal.ShardedMPPMBridge

/-!
# Final External-Certificate Endpoint

The theorem `arbitrarily_large_twins` is unconditional inside Lean after
importing the generated sharded MP/PM overflow certificate.  Its sole non-Lean
dependency is the route-realization declaration named
`external_shardedPredictedEvents_realized_of_cofinalTail`; the overflow count is
checked by Lean from the generated shard modules.
-/

namespace TwinPrimeExternal

theorem no_cofinalExceptionTail :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_shardedMPPMCertificate

theorem not_boundedTwinMids : Not BoundedTwinMids :=
  no_boundedTwinMids_of_no_cofinalExceptionTail no_cofinalExceptionTail

theorem arbitrarily_large_twins : ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    no_cofinalExceptionTail

end TwinPrimeExternal
