import TwinPrimeExternal.GeneratedCertificate
import TwinPrimeExternal.GeneratedShardedMPPM.Index

/-!
# Bridge from the Sharded MP/PM Count Certificate

This file connects the generated sharded interval certificate to the existing
endpoint constants.  It does not yet replace the external route-realization
assumption, but it does replace the fragile "just trust the count" part with a
Lean-checked, cached shard manifest.
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

end TwinPrimeExternal
