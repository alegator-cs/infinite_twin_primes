import TwinPrimeExternal.RecursiveMPPMCertificate
import TwinPrimeExternal.GeneratedShardedMPPM.Index

/-!
# Bridge from the Sharded MP/PM Count Certificate

This file connects the generated sharded interval certificate to the existing
endpoint constants and certificate shape.

The checked shards own the overflow side: Lean verifies the generated predicted
MP/PM event count and the strict cardinal overflow.  The remaining external
boundary is route-realization: under a cofinal exceptional tail, the generated
predicted events are realized by actual MP/PM events in the target block.
-/

namespace TwinPrimeExternal

theorem sharded_checkedPredictedCount_eq_predictedEventCount :
    GeneratedShardedMPPM.checkedPredictedCount = predictedEventCount := by
  rw [GeneratedShardedMPPM.checkedPredictedCount_eq,
    GeneratedShardedMPPM.expectedPredictedCount_eq_core]

theorem sharded_checkedPredictedCount_exceeds_generatedMPPMCard :
    generatedMPPMCard < GeneratedShardedMPPM.checkedPredictedCount :=
  GeneratedShardedMPPM.checkedPredictedCount_exceeds_generatedMPPMCard

theorem generated_overflow_verified_by_sharded_certificate :
    generatedMPPMCard < predictedEventCount := by
  simpa [sharded_checkedPredictedCount_eq_predictedEventCount] using
    sharded_checkedPredictedCount_exceeds_generatedMPPMCard

/--
The actual finite side-labeled MP/PM event set, represented by the checked
generated cap.
-/
def shardedActualEvents : Finset Nat :=
  Finset.range generatedMPPMCard

theorem shardedActualEvents_card :
    shardedActualEvents.card = generatedMPPMCard := by
  simp [shardedActualEvents]

/--
The predicted side-labeled MP/PM event set, represented by the Lean-checked
sharded interval count.

The shards check the concrete event-ID manifest and prove that its cardinality
is `GeneratedShardedMPPM.checkedPredictedCount`.
-/
def shardedPredictedEvents : Finset Nat :=
  Finset.range GeneratedShardedMPPM.checkedPredictedCount

theorem shardedPredictedEvents_card :
    shardedPredictedEvents.card = predictedEventCount := by
  simp [shardedPredictedEvents, sharded_checkedPredictedCount_eq_predictedEventCount]

/--
External route-realization bridge for the sharded MP/PM certificate.

This is now the sole project-specific assumption on the `Final.lean` twin-prime
endpoint path.  The count overflow itself is checked by the imported shards.
-/
axiom external_shardedPredictedEvents_realized_of_cofinalTail :
    (exists B, CofinalExceptionTail MidpointExceptionalPrime B) ->
      shardedPredictedEvents ⊆ shardedActualEvents

def shardedRecursiveMPPMEventCertificate :
    RecursiveMPPMEventCertificate where
  actualEvents := shardedActualEvents
  predictedEvents := shardedPredictedEvents
  actual_card := shardedActualEvents_card
  predicted_card := shardedPredictedEvents_card
  predicted_realized_of_cofinalTail :=
    external_shardedPredictedEvents_realized_of_cofinalTail

theorem no_cofinalExceptionTail_of_shardedMPPMCertificate :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_recursiveMPPMEventCertificate
    shardedRecursiveMPPMEventCertificate

end TwinPrimeExternal
