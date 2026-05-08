import TwinPrimeExternal.GeneratedShardedMPPM.Shard000
import TwinPrimeExternal.GeneratedShardedMPPM.Shard001
import TwinPrimeExternal.GeneratedShardedMPPM.Shard002
import TwinPrimeExternal.GeneratedShardedMPPM.Shard003
import TwinPrimeExternal.GeneratedShardedMPPM.Shard004
import TwinPrimeExternal.GeneratedShardedMPPM.Shard005
import TwinPrimeExternal.GeneratedShardedMPPM.Shard006
import TwinPrimeExternal.GeneratedShardedMPPM.Shard007
import TwinPrimeExternal.GeneratedShardedMPPM.Shard008
import TwinPrimeExternal.GeneratedShardedMPPM.Shard009
import TwinPrimeExternal.GeneratedShardedMPPM.Shard010
import TwinPrimeExternal.GeneratedShardedMPPM.Shard011
import TwinPrimeExternal.GeneratedShardedMPPM.Shard012
import TwinPrimeExternal.GeneratedShardedMPPM.Shard013
import TwinPrimeExternal.GeneratedShardedMPPM.Shard014
import TwinPrimeExternal.GeneratedShardedMPPM.Shard015
import TwinPrimeExternal.GeneratedShardedMPPM.Shard016
import TwinPrimeExternal.GeneratedShardedMPPM.Shard017
import TwinPrimeExternal.GeneratedShardedMPPM.Shard018
import TwinPrimeExternal.GeneratedShardedMPPM.Shard019
import TwinPrimeExternal.GeneratedShardedMPPM.Shard020
import TwinPrimeExternal.GeneratedShardedMPPM.Shard021
import TwinPrimeExternal.GeneratedShardedMPPM.Shard022
import TwinPrimeExternal.GeneratedShardedMPPM.Shard023
import TwinPrimeExternal.GeneratedShardedMPPM.Shard024
import TwinPrimeExternal.GeneratedShardedMPPM.Shard025
import TwinPrimeExternal.GeneratedShardedMPPM.Shard026
import TwinPrimeExternal.GeneratedShardedMPPM.Shard027
import TwinPrimeExternal.GeneratedShardedMPPM.Shard028
import TwinPrimeExternal.GeneratedShardedMPPM.Shard029
import TwinPrimeExternal.GeneratedShardedMPPM.Shard030
import TwinPrimeExternal.GeneratedShardedMPPM.Shard031
import TwinPrimeExternal.GeneratedShardedMPPM.Shard032
import TwinPrimeExternal.GeneratedShardedMPPM.Shard033
import TwinPrimeExternal.GeneratedShardedMPPM.Shard034
import TwinPrimeExternal.GeneratedShardedMPPM.Shard035
import TwinPrimeExternal.GeneratedShardedMPPM.Shard036
import TwinPrimeExternal.GeneratedShardedMPPM.Shard037
import TwinPrimeExternal.GeneratedShardedMPPM.Shard038
import TwinPrimeExternal.GeneratedShardedMPPM.Shard039
import TwinPrimeExternal.GeneratedShardedMPPM.Shard040
import TwinPrimeExternal.GeneratedShardedMPPM.Shard041
import TwinPrimeExternal.GeneratedShardedMPPM.Shard042
import TwinPrimeExternal.GeneratedShardedMPPM.Shard043
import TwinPrimeExternal.GeneratedShardedMPPM.Shard044
import TwinPrimeExternal.GeneratedShardedMPPM.Shard045
import TwinPrimeExternal.GeneratedShardedMPPM.Shard046
import TwinPrimeExternal.GeneratedShardedMPPM.Shard047
import TwinPrimeExternal.GeneratedShardedMPPM.Shard048
import TwinPrimeExternal.GeneratedShardedMPPM.Shard049
import TwinPrimeExternal.GeneratedShardedMPPM.Shard050
import TwinPrimeExternal.GeneratedShardedMPPM.Shard051
import TwinPrimeExternal.GeneratedShardedMPPM.Shard052
import TwinPrimeExternal.GeneratedShardedMPPM.Shard053
import TwinPrimeExternal.GeneratedShardedMPPM.Shard054
import TwinPrimeExternal.GeneratedShardedMPPM.Shard055
import TwinPrimeExternal.GeneratedShardedMPPM.Shard056
import TwinPrimeExternal.GeneratedShardedMPPM.Shard057

/-!
# Generated Sharded MP/PM Overflow Certificate

This manifest imports interval shards for the generated overflow event IDs.
Lean checks each interval shard independently and checks the global count
arithmetic here.
-/

namespace TwinPrimeExternal.GeneratedShardedMPPM

def shardCount : Nat := 58
def actualCap : Nat := 95568
def expectedPredictedCount : Nat := 181052
def expectedActualPredictedCount : Nat := 65419
def expectedFalsePredictedCount : Nat := 115633

def checkedPredictedCount : Nat :=
  Shard000.checkedEventCount +
  Shard001.checkedEventCount +
  Shard002.checkedEventCount +
  Shard003.checkedEventCount +
  Shard004.checkedEventCount +
  Shard005.checkedEventCount +
  Shard006.checkedEventCount +
  Shard007.checkedEventCount +
  Shard008.checkedEventCount +
  Shard009.checkedEventCount +
  Shard010.checkedEventCount +
  Shard011.checkedEventCount +
  Shard012.checkedEventCount +
  Shard013.checkedEventCount +
  Shard014.checkedEventCount +
  Shard015.checkedEventCount +
  Shard016.checkedEventCount +
  Shard017.checkedEventCount +
  Shard018.checkedEventCount +
  Shard019.checkedEventCount +
  Shard020.checkedEventCount +
  Shard021.checkedEventCount +
  Shard022.checkedEventCount +
  Shard023.checkedEventCount +
  Shard024.checkedEventCount +
  Shard025.checkedEventCount +
  Shard026.checkedEventCount +
  Shard027.checkedEventCount +
  Shard028.checkedEventCount +
  Shard029.checkedEventCount +
  Shard030.checkedEventCount +
  Shard031.checkedEventCount +
  Shard032.checkedEventCount +
  Shard033.checkedEventCount +
  Shard034.checkedEventCount +
  Shard035.checkedEventCount +
  Shard036.checkedEventCount +
  Shard037.checkedEventCount +
  Shard038.checkedEventCount +
  Shard039.checkedEventCount +
  Shard040.checkedEventCount +
  Shard041.checkedEventCount +
  Shard042.checkedEventCount +
  Shard043.checkedEventCount +
  Shard044.checkedEventCount +
  Shard045.checkedEventCount +
  Shard046.checkedEventCount +
  Shard047.checkedEventCount +
  Shard048.checkedEventCount +
  Shard049.checkedEventCount +
  Shard050.checkedEventCount +
  Shard051.checkedEventCount +
  Shard052.checkedEventCount +
  Shard053.checkedEventCount +
  Shard054.checkedEventCount +
  Shard055.checkedEventCount +
  Shard056.checkedEventCount +
  Shard057.checkedEventCount

theorem checkedPredictedCount_eq :
    checkedPredictedCount = expectedPredictedCount := by
  norm_num [checkedPredictedCount, expectedPredictedCount, Shard000.checkedEventCount, Shard001.checkedEventCount, Shard002.checkedEventCount, Shard003.checkedEventCount, Shard004.checkedEventCount, Shard005.checkedEventCount, Shard006.checkedEventCount, Shard007.checkedEventCount, Shard008.checkedEventCount, Shard009.checkedEventCount, Shard010.checkedEventCount, Shard011.checkedEventCount, Shard012.checkedEventCount, Shard013.checkedEventCount, Shard014.checkedEventCount, Shard015.checkedEventCount, Shard016.checkedEventCount, Shard017.checkedEventCount, Shard018.checkedEventCount, Shard019.checkedEventCount, Shard020.checkedEventCount, Shard021.checkedEventCount, Shard022.checkedEventCount, Shard023.checkedEventCount, Shard024.checkedEventCount, Shard025.checkedEventCount, Shard026.checkedEventCount, Shard027.checkedEventCount, Shard028.checkedEventCount, Shard029.checkedEventCount, Shard030.checkedEventCount, Shard031.checkedEventCount, Shard032.checkedEventCount, Shard033.checkedEventCount, Shard034.checkedEventCount, Shard035.checkedEventCount, Shard036.checkedEventCount, Shard037.checkedEventCount, Shard038.checkedEventCount, Shard039.checkedEventCount, Shard040.checkedEventCount, Shard041.checkedEventCount, Shard042.checkedEventCount, Shard043.checkedEventCount, Shard044.checkedEventCount, Shard045.checkedEventCount, Shard046.checkedEventCount, Shard047.checkedEventCount, Shard048.checkedEventCount, Shard049.checkedEventCount, Shard050.checkedEventCount, Shard051.checkedEventCount, Shard052.checkedEventCount, Shard053.checkedEventCount, Shard054.checkedEventCount, Shard055.checkedEventCount, Shard056.checkedEventCount, Shard057.checkedEventCount]

theorem expectedPredictedCount_eq_core :
    expectedPredictedCount = TwinPrimeExternal.predictedEventCount := by
  norm_num [expectedPredictedCount, TwinPrimeExternal.predictedEventCount]

theorem actualCap_eq_core :
    actualCap = TwinPrimeExternal.generatedMPPMCard := by
  norm_num [actualCap, TwinPrimeExternal.generatedMPPMCard]

theorem checkedPredictedCount_exceeds_actualCap :
    actualCap < checkedPredictedCount := by
  norm_num [actualCap, checkedPredictedCount, Shard000.checkedEventCount, Shard001.checkedEventCount, Shard002.checkedEventCount, Shard003.checkedEventCount, Shard004.checkedEventCount, Shard005.checkedEventCount, Shard006.checkedEventCount, Shard007.checkedEventCount, Shard008.checkedEventCount, Shard009.checkedEventCount, Shard010.checkedEventCount, Shard011.checkedEventCount, Shard012.checkedEventCount, Shard013.checkedEventCount, Shard014.checkedEventCount, Shard015.checkedEventCount, Shard016.checkedEventCount, Shard017.checkedEventCount, Shard018.checkedEventCount, Shard019.checkedEventCount, Shard020.checkedEventCount, Shard021.checkedEventCount, Shard022.checkedEventCount, Shard023.checkedEventCount, Shard024.checkedEventCount, Shard025.checkedEventCount, Shard026.checkedEventCount, Shard027.checkedEventCount, Shard028.checkedEventCount, Shard029.checkedEventCount, Shard030.checkedEventCount, Shard031.checkedEventCount, Shard032.checkedEventCount, Shard033.checkedEventCount, Shard034.checkedEventCount, Shard035.checkedEventCount, Shard036.checkedEventCount, Shard037.checkedEventCount, Shard038.checkedEventCount, Shard039.checkedEventCount, Shard040.checkedEventCount, Shard041.checkedEventCount, Shard042.checkedEventCount, Shard043.checkedEventCount, Shard044.checkedEventCount, Shard045.checkedEventCount, Shard046.checkedEventCount, Shard047.checkedEventCount, Shard048.checkedEventCount, Shard049.checkedEventCount, Shard050.checkedEventCount, Shard051.checkedEventCount, Shard052.checkedEventCount, Shard053.checkedEventCount, Shard054.checkedEventCount, Shard055.checkedEventCount, Shard056.checkedEventCount, Shard057.checkedEventCount]

theorem checkedPredictedCount_exceeds_generatedMPPMCard :
    TwinPrimeExternal.generatedMPPMCard < checkedPredictedCount := by
  simpa [actualCap_eq_core] using checkedPredictedCount_exceeds_actualCap

theorem shard_boundaries_strict :
    True /\ Shard000.lastId < Shard001.firstId /\ Shard001.lastId < Shard002.firstId /\ Shard002.lastId < Shard003.firstId /\ Shard003.lastId < Shard004.firstId /\ Shard004.lastId < Shard005.firstId /\ Shard005.lastId < Shard006.firstId /\ Shard006.lastId < Shard007.firstId /\ Shard007.lastId < Shard008.firstId /\ Shard008.lastId < Shard009.firstId /\ Shard009.lastId < Shard010.firstId /\ Shard010.lastId < Shard011.firstId /\ Shard011.lastId < Shard012.firstId /\ Shard012.lastId < Shard013.firstId /\ Shard013.lastId < Shard014.firstId /\ Shard014.lastId < Shard015.firstId /\ Shard015.lastId < Shard016.firstId /\ Shard016.lastId < Shard017.firstId /\ Shard017.lastId < Shard018.firstId /\ Shard018.lastId < Shard019.firstId /\ Shard019.lastId < Shard020.firstId /\ Shard020.lastId < Shard021.firstId /\ Shard021.lastId < Shard022.firstId /\ Shard022.lastId < Shard023.firstId /\ Shard023.lastId < Shard024.firstId /\ Shard024.lastId < Shard025.firstId /\ Shard025.lastId < Shard026.firstId /\ Shard026.lastId < Shard027.firstId /\ Shard027.lastId < Shard028.firstId /\ Shard028.lastId < Shard029.firstId /\ Shard029.lastId < Shard030.firstId /\ Shard030.lastId < Shard031.firstId /\ Shard031.lastId < Shard032.firstId /\ Shard032.lastId < Shard033.firstId /\ Shard033.lastId < Shard034.firstId /\ Shard034.lastId < Shard035.firstId /\ Shard035.lastId < Shard036.firstId /\ Shard036.lastId < Shard037.firstId /\ Shard037.lastId < Shard038.firstId /\ Shard038.lastId < Shard039.firstId /\ Shard039.lastId < Shard040.firstId /\ Shard040.lastId < Shard041.firstId /\ Shard041.lastId < Shard042.firstId /\ Shard042.lastId < Shard043.firstId /\ Shard043.lastId < Shard044.firstId /\ Shard044.lastId < Shard045.firstId /\ Shard045.lastId < Shard046.firstId /\ Shard046.lastId < Shard047.firstId /\ Shard047.lastId < Shard048.firstId /\ Shard048.lastId < Shard049.firstId /\ Shard049.lastId < Shard050.firstId /\ Shard050.lastId < Shard051.firstId /\ Shard051.lastId < Shard052.firstId /\ Shard052.lastId < Shard053.firstId /\ Shard053.lastId < Shard054.firstId /\ Shard054.lastId < Shard055.firstId /\ Shard055.lastId < Shard056.firstId /\ Shard056.lastId < Shard057.firstId := by
  norm_num [Shard000.firstId, Shard000.lastId, Shard001.firstId, Shard001.lastId, Shard002.firstId, Shard002.lastId, Shard003.firstId, Shard003.lastId, Shard004.firstId, Shard004.lastId, Shard005.firstId, Shard005.lastId, Shard006.firstId, Shard006.lastId, Shard007.firstId, Shard007.lastId, Shard008.firstId, Shard008.lastId, Shard009.firstId, Shard009.lastId, Shard010.firstId, Shard010.lastId, Shard011.firstId, Shard011.lastId, Shard012.firstId, Shard012.lastId, Shard013.firstId, Shard013.lastId, Shard014.firstId, Shard014.lastId, Shard015.firstId, Shard015.lastId, Shard016.firstId, Shard016.lastId, Shard017.firstId, Shard017.lastId, Shard018.firstId, Shard018.lastId, Shard019.firstId, Shard019.lastId, Shard020.firstId, Shard020.lastId, Shard021.firstId, Shard021.lastId, Shard022.firstId, Shard022.lastId, Shard023.firstId, Shard023.lastId, Shard024.firstId, Shard024.lastId, Shard025.firstId, Shard025.lastId, Shard026.firstId, Shard026.lastId, Shard027.firstId, Shard027.lastId, Shard028.firstId, Shard028.lastId, Shard029.firstId, Shard029.lastId, Shard030.firstId, Shard030.lastId, Shard031.firstId, Shard031.lastId, Shard032.firstId, Shard032.lastId, Shard033.firstId, Shard033.lastId, Shard034.firstId, Shard034.lastId, Shard035.firstId, Shard035.lastId, Shard036.firstId, Shard036.lastId, Shard037.firstId, Shard037.lastId, Shard038.firstId, Shard038.lastId, Shard039.firstId, Shard039.lastId, Shard040.firstId, Shard040.lastId, Shard041.firstId, Shard041.lastId, Shard042.firstId, Shard042.lastId, Shard043.firstId, Shard043.lastId, Shard044.firstId, Shard044.lastId, Shard045.firstId, Shard045.lastId, Shard046.firstId, Shard046.lastId, Shard047.firstId, Shard047.lastId, Shard048.firstId, Shard048.lastId, Shard049.firstId, Shard049.lastId, Shard050.firstId, Shard050.lastId, Shard051.firstId, Shard051.lastId, Shard052.firstId, Shard052.lastId, Shard053.firstId, Shard053.lastId, Shard054.firstId, Shard054.lastId, Shard055.firstId, Shard055.lastId, Shard056.firstId, Shard056.lastId, Shard057.firstId, Shard057.lastId]

end TwinPrimeExternal.GeneratedShardedMPPM
