import TwinPrimeExternal.RecursiveMPPMCertificate

/-!
# Sharded MP/PM Certificate Helpers

The generated sharded certificate files use these tiny predicates to keep each
shard locally checkable.  C++ emits the data, but Lean checks:

* lengths;
* actual/false event counts;
* sorted unique event IDs inside each shard;
* manifest arithmetic across shards.
-/

namespace TwinPrimeExternal.ShardedMPPMCertificate

def StrictlyIncreasing (xs : List Nat) : Prop :=
  xs.Pairwise (fun a b => a < b)

theorem nodup_of_strictlyIncreasing
    {xs : List Nat}
    (h : StrictlyIncreasing xs) :
    xs.Nodup :=
  h.imp (fun hlt => ne_of_lt hlt)

def intervalLength (interval : Nat × Nat) : Nat :=
  interval.2 - interval.1 + 1

end TwinPrimeExternal.ShardedMPPMCertificate
