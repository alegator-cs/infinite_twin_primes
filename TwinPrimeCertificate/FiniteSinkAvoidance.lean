import TwinPrimeCertificate.Core

/-!
# Finite Sink Avoidance

This file formalizes the deterministic part of the reverse-sink argument.

The intended analytic/computational input is:

* there are arbitrarily large usable split seeds;
* each such seed has a legal quadratic row that avoids a fixed finite old
  MP/PM sink;
* if that seed is midpoint-exceptional, the avoiding row forces a finite event
  outside the sink.

The Lean theorem below proves that those facts are incompatible with a cofinal
exceptional tail.  In prose: a finite old sink may have infinitely many
ancestors, but it cannot absorb every sufficiently large usable prime once an
escaping residue class is available.
-/

namespace TwinPrimeCertificate

/--
Finite ancestor sets cannot contain all sufficiently large eligible split-prime
seeds.

This is the fully formal version of the slogan: infinitely many ancestors may
exist, but a fixed finite ancestor trap cannot be every sufficiently large
eligible prime.
-/
theorem finite_ancestor_set_misses_arbitrarily_large_modFiveOnePrime
    (ancestors : Finset Nat) (N : Nat) :
    ∃ p, N < p ∧ ModFiveOnePrime p ∧ p ∉ ancestors :=
  exists_modFiveOnePrime_gt_not_mem_finset ancestors N

/--
A fixed finite ancestor set cannot contain a cofinal eligible-prime tail.
-/
theorem finite_ancestor_set_not_cofinal_for_modFiveOnePrimes
    (ancestors : Finset Nat) :
    ¬ ∃ B,
      ∀ p, B < p -> ModFiveOnePrime p -> p ∈ ancestors :=
  not_cofinal_modFiveOnePrimes_subset_finset ancestors

/--
There are arbitrarily large finite batches of eligible split primes.

This is just the finite-set strengthening of
`exists_modFiveOnePrime_gt_not_mem_finset`: repeatedly choose a new eligible
prime outside the batch already built.
-/
theorem exists_modFiveOnePrime_batch_after (N n : Nat) :
    ∃ seeds : Finset Nat,
      n ≤ seeds.card ∧
        ∀ p, p ∈ seeds -> N < p ∧ ModFiveOnePrime p := by
  classical
  induction n with
  | zero =>
      refine ⟨∅, by simp, ?_⟩
      intro p hp
      simp at hp
  | succ n ih =>
      rcases ih with ⟨seeds, hcard, hmem⟩
      rcases exists_modFiveOnePrime_gt_not_mem_finset seeds N with
        ⟨p, hpgt, hpSeed, hpNotMem⟩
      refine ⟨insert p seeds, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hpNotMem]
        omega
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact ⟨hpgt, hpSeed⟩
        · exact hmem q hq

/--
A finite reverse-sink avoidance certificate.

`ForcedEvent p event` is the semantic relation saying that the exceptional seed
`p` forces the side-event `event` by the chosen quadratic descent.  The
certificate separates the two relevant facts:

* `escaping_seed_forces_event_outside_sink`: an escaping seed forces some event
  outside the finite sink;
* `terminal_sink`: if a cofinal tail were completely absorbed by this finite
  sink, every forced event from such a seed would have to lie inside the sink.

Those two statements contradict each other for any sufficiently large escaping
seed supplied by `exists_escaping_seed_after`.
-/
structure FiniteSinkAvoidanceCertificate where
  sink : Finset Nat
  threshold : Nat
  EscapingSeed : Nat -> Prop
  ForcedEvent : Nat -> Nat -> Prop
  exists_escaping_seed_after :
    ∀ N,
      ∃ p,
        N < p ∧
          threshold < p ∧
            ModFiveOnePrime p ∧
              EscapingSeed p
  escaping_seed_forces_event_outside_sink :
    ∀ p,
      threshold < p ->
        ModFiveOnePrime p ->
          EscapingSeed p ->
            MidpointExceptionalPrime p ->
              ∃ event,
                ForcedEvent p event ∧
                  event ∉ sink
  terminal_sink :
    ∀ p event,
      threshold < p ->
        ModFiveOnePrime p ->
          EscapingSeed p ->
            MidpointExceptionalPrime p ->
              ForcedEvent p event ->
                event ∈ sink

/--
Finite reverse sinks cannot absorb a cofinal exceptional tail when arbitrarily
large escaping split seeds exist.
-/
theorem no_cofinalExceptionTail_of_finiteSinkAvoidance
    (cert : FiniteSinkAvoidanceCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  intro htail
  rcases htail with ⟨B, tail⟩
  rcases cert.exists_escaping_seed_after (max B cert.threshold) with
    ⟨p, hpgt, hpThreshold, hpSeed, hpEscape⟩
  have hBp : B < p :=
    lt_of_le_of_lt (le_max_left B cert.threshold) hpgt
  have hpExceptional : MidpointExceptionalPrime p :=
    tail p hpSeed.1 hBp
  rcases cert.escaping_seed_forces_event_outside_sink
      p hpThreshold hpSeed hpEscape hpExceptional with
    ⟨event, hForced, hNotSink⟩
  have hSink : event ∈ cert.sink :=
    cert.terminal_sink
      p event hpThreshold hpSeed hpEscape hpExceptional hForced
  exact hNotSink hSink

/--
The finite-sink avoidance certificate is enough for the final twin-prime
endpoint, through the existing no-cofinal-tail bridge.
-/
theorem arbitrarily_large_twins_of_finiteSinkAvoidance
    (cert : FiniteSinkAvoidanceCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_finiteSinkAvoidance cert)

/--
Residue-level version of finite sink avoidance.

`badResidues` is the finite set of root residues that route into the old sink.
`rootResidue` records the residue class of the chosen quadratic root for a
seed.  The supply field is the analytic/computational input: arbitrarily far
out there is a usable split prime whose chosen root avoids the finite bad set.

This structure is closer to the intended proof by quadratic-root
equidistribution: prove `escaping_root_after` by showing that the finite bad
set is not locally total and that quadratic roots occur infinitely often in an
allowed class.
-/
structure ResidueFiniteSinkAvoidanceCertificate where
  sink : Finset Nat
  threshold : Nat
  modulus : Nat
  badResidues : Finset Nat
  rootResidue : Nat -> Nat
  ForcedEvent : Nat -> Nat -> Prop
  escaping_root_after :
    ∀ N,
      ∃ p,
        N < p ∧
          threshold < p ∧
            ModFiveOnePrime p ∧
              rootResidue p < modulus ∧
                rootResidue p ∉ badResidues
  root_outside_bad_forces_event_outside_sink :
    ∀ p,
      threshold < p ->
        ModFiveOnePrime p ->
          rootResidue p < modulus ->
            rootResidue p ∉ badResidues ->
              MidpointExceptionalPrime p ->
                ∃ event,
                  ForcedEvent p event ∧
                    event ∉ sink
  terminal_sink :
    ∀ p event,
      threshold < p ->
        ModFiveOnePrime p ->
          rootResidue p < modulus ->
            rootResidue p ∉ badResidues ->
              MidpointExceptionalPrime p ->
                ForcedEvent p event ->
                  event ∈ sink

/--
The residue-level certificate implies the finite-sink certificate.
-/
def ResidueFiniteSinkAvoidanceCertificate.toFiniteSinkAvoidance
    (cert : ResidueFiniteSinkAvoidanceCertificate) :
    FiniteSinkAvoidanceCertificate where
  sink := cert.sink
  threshold := cert.threshold
  EscapingSeed := fun p =>
    cert.rootResidue p < cert.modulus ∧
      cert.rootResidue p ∉ cert.badResidues
  ForcedEvent := cert.ForcedEvent
  exists_escaping_seed_after := by
    intro N
    rcases cert.escaping_root_after N with
      ⟨p, hpgt, hpThreshold, hpSeed, hrootLt, hrootBad⟩
    exact ⟨p, hpgt, hpThreshold, hpSeed, hrootLt, hrootBad⟩
  escaping_seed_forces_event_outside_sink := by
    intro p hpThreshold hpSeed hpEscape hpExceptional
    exact cert.root_outside_bad_forces_event_outside_sink
      p hpThreshold hpSeed hpEscape.1 hpEscape.2 hpExceptional
  terminal_sink := by
    intro p event hpThreshold hpSeed hpEscape hpExceptional hForced
    exact cert.terminal_sink
      p event hpThreshold hpSeed hpEscape.1 hpEscape.2
      hpExceptional hForced

theorem no_cofinalExceptionTail_of_residueFiniteSinkAvoidance
    (cert : ResidueFiniteSinkAvoidanceCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_finiteSinkAvoidance
    cert.toFiniteSinkAvoidance

theorem arbitrarily_large_twins_of_residueFiniteSinkAvoidance
    (cert : ResidueFiniteSinkAvoidanceCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_finiteSinkAvoidance
    cert.toFiniteSinkAvoidance

/-!
## Multiplicity-Free Terminal Slot Sink

This is the stripped-down endpoint suggested by the expanding-window picture.
Multiplicity is irrelevant: a fixed finite terminal slot set can absorb
arbitrarily many starts only by collision, but finite-sink freshness asks for a
single later exceptional seed forcing an event outside that finite set.

The two semantic inputs are intentionally narrow:

* `exists_fresh_forced_event_after`: after any bound, some usable seed forces a
  terminal event outside the chosen finite slot set, if it is exceptional;
* `all_forced_events_land_in_slots`: under the terminal-tail interpretation,
  every forced terminal event from such a seed lands inside the same slot set.

Together they contradict a cofinal exceptional tail.  No multiplicity bound is
needed.
-/

structure TerminalSlotSinkCertificate where
  slots : Finset Nat
  threshold : Nat
  ForcedEvent : Nat -> Nat -> Prop
  exists_fresh_forced_event_after :
    ∀ N,
      ∃ p,
        N < p ∧
          threshold < p ∧
            ModFiveOnePrime p ∧
              (MidpointExceptionalPrime p ->
                ∃ event, ForcedEvent p event ∧ event ∉ slots)
  all_forced_events_land_in_slots :
    ∀ p event,
      threshold < p ->
        ModFiveOnePrime p ->
          MidpointExceptionalPrime p ->
            ForcedEvent p event ->
              event ∈ slots

theorem no_cofinalExceptionTail_of_terminalSlotSink
    (cert : TerminalSlotSinkCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  intro htail
  rcases htail with ⟨B, tail⟩
  rcases cert.exists_fresh_forced_event_after (max B cert.threshold) with
    ⟨p, hpgt, hpThreshold, hpSeed, hfresh⟩
  have hBp : B < p :=
    lt_of_le_of_lt (le_max_left B cert.threshold) hpgt
  have hpExceptional : MidpointExceptionalPrime p :=
    tail p hpSeed.1 hBp
  rcases hfresh hpExceptional with ⟨event, hForced, hNotSlot⟩
  have hSlot : event ∈ cert.slots :=
    cert.all_forced_events_land_in_slots
      p event hpThreshold hpSeed hpExceptional hForced
  exact hNotSlot hSlot

theorem arbitrarily_large_twins_of_terminalSlotSink
    (cert : TerminalSlotSinkCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_terminalSlotSink cert)

/-!
## Ancestor Freshness to Terminal-Event Freshness

This is the bridge from the already-proved finite-ancestor theorem to the
terminal-slot sink formulation.

For a finite terminal slot set, collect every seed ancestor of every slot into
one finite set.  Mathlib/Dirichlet supplies an arbitrarily large eligible
prime outside that finite ancestor union.  If an exceptional seed always forces
some terminal event, and every in-slot forced event records the seed in that
slot's ancestor set, then the forced event cannot be in the slot set.  If the
terminal-tail interpretation says all forced terminal events are in the slot
set, contradiction.
-/

def slotAncestorUnion
    (slots : Finset Nat) (ancestorsOf : Nat -> Finset Nat) : Finset Nat :=
  slots.biUnion ancestorsOf

structure TerminalSlotAncestorBridgeCertificate where
  slots : Finset Nat
  threshold : Nat
  ancestorsOf : Nat -> Finset Nat
  ForcedEvent : Nat -> Nat -> Prop
  forced_event_of_exception :
    ∀ p,
      threshold < p ->
        ModFiveOnePrime p ->
          MidpointExceptionalPrime p ->
            ∃ event, ForcedEvent p event
  event_in_slot_imp_seed_in_ancestors :
    ∀ p event,
      threshold < p ->
        ModFiveOnePrime p ->
          MidpointExceptionalPrime p ->
            ForcedEvent p event ->
              event ∈ slots ->
                p ∈ ancestorsOf event
  all_forced_events_land_in_slots :
    ∀ p event,
      threshold < p ->
        ModFiveOnePrime p ->
          MidpointExceptionalPrime p ->
            ForcedEvent p event ->
              event ∈ slots

theorem no_cofinalExceptionTail_of_terminalSlotAncestorBridge
    (cert : TerminalSlotAncestorBridgeCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  classical
  intro htail
  rcases htail with ⟨B, tail⟩
  let ancestorUnion := slotAncestorUnion cert.slots cert.ancestorsOf
  rcases exists_modFiveOnePrime_gt_not_mem_finset
      ancestorUnion (max B cert.threshold) with
    ⟨p, hpgt, hpSeed, hpNotAncestor⟩
  have hpThreshold : cert.threshold < p :=
    lt_of_le_of_lt (le_max_right B cert.threshold) hpgt
  have hBp : B < p :=
    lt_of_le_of_lt (le_max_left B cert.threshold) hpgt
  have hpExceptional : MidpointExceptionalPrime p :=
    tail p hpSeed.1 hBp
  rcases cert.forced_event_of_exception
      p hpThreshold hpSeed hpExceptional with
    ⟨event, hForced⟩
  have hSlot : event ∈ cert.slots :=
    cert.all_forced_events_land_in_slots
      p event hpThreshold hpSeed hpExceptional hForced
  have hpInEventAncestors : p ∈ cert.ancestorsOf event :=
    cert.event_in_slot_imp_seed_in_ancestors
      p event hpThreshold hpSeed hpExceptional hForced hSlot
  have hpInUnion : p ∈ ancestorUnion := by
    change p ∈ slotAncestorUnion cert.slots cert.ancestorsOf
    rw [slotAncestorUnion, Finset.mem_biUnion]
    exact ⟨event, hSlot, hpInEventAncestors⟩
  exact hpNotAncestor hpInUnion

theorem arbitrarily_large_twins_of_terminalSlotAncestorBridge
    (cert : TerminalSlotAncestorBridgeCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_terminalSlotAncestorBridge cert)

/-!
## Moving Terminal Windows

The previous certificate uses one fixed finite terminal slot set.  For the
tail-start picture, the natural finite set depends on the supposed beginning
`B` of the cofinal exceptional tail: take all terminal slots in the window up
to `B`.

This version proves the same contradiction while allowing `slots B` and the
declared ancestor sets to depend on the tail start.
-/

def movingSlotAncestorUnion
    (slots : Nat -> Finset Nat)
    (ancestorsOf : Nat -> Nat -> Finset Nat)
    (B : Nat) : Finset Nat :=
  (slots B).biUnion (ancestorsOf B)

structure MovingTerminalSlotAncestorBridgeCertificate where
  threshold : Nat
  slots : Nat -> Finset Nat
  ancestorsOf : Nat -> Nat -> Finset Nat
  ForcedEvent : Nat -> Nat -> Prop
  forced_event_of_exception :
    ∀ B p,
      B < p ->
        threshold < p ->
          ModFiveOnePrime p ->
            MidpointExceptionalPrime p ->
              ∃ event, ForcedEvent p event
  event_in_window_imp_seed_in_ancestors :
    ∀ B p event,
      B < p ->
        threshold < p ->
          ModFiveOnePrime p ->
            MidpointExceptionalPrime p ->
              ForcedEvent p event ->
                event ∈ slots B ->
                  p ∈ ancestorsOf B event
  all_forced_events_land_in_window :
    ∀ B p event,
      B < p ->
        threshold < p ->
          ModFiveOnePrime p ->
            MidpointExceptionalPrime p ->
              ForcedEvent p event ->
                event ∈ slots B

theorem no_cofinalExceptionTail_of_movingTerminalSlotAncestorBridge
    (cert : MovingTerminalSlotAncestorBridgeCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  classical
  intro htail
  rcases htail with ⟨B, tail⟩
  let ancestorUnion :=
    movingSlotAncestorUnion cert.slots cert.ancestorsOf B
  rcases exists_modFiveOnePrime_gt_not_mem_finset
      ancestorUnion (max B cert.threshold) with
    ⟨p, hpgt, hpSeed, hpNotAncestor⟩
  have hpThreshold : cert.threshold < p :=
    lt_of_le_of_lt (le_max_right B cert.threshold) hpgt
  have hBp : B < p :=
    lt_of_le_of_lt (le_max_left B cert.threshold) hpgt
  have hpExceptional : MidpointExceptionalPrime p :=
    tail p hpSeed.1 hBp
  rcases cert.forced_event_of_exception
      B p hBp hpThreshold hpSeed hpExceptional with
    ⟨event, hForced⟩
  have hSlot : event ∈ cert.slots B :=
    cert.all_forced_events_land_in_window
      B p event hBp hpThreshold hpSeed hpExceptional hForced
  have hpInEventAncestors : p ∈ cert.ancestorsOf B event :=
    cert.event_in_window_imp_seed_in_ancestors
      B p event hBp hpThreshold hpSeed hpExceptional hForced hSlot
  have hpInUnion : p ∈ ancestorUnion := by
    change p ∈ movingSlotAncestorUnion cert.slots cert.ancestorsOf B
    rw [movingSlotAncestorUnion, Finset.mem_biUnion]
    exact ⟨event, hSlot, hpInEventAncestors⟩
  exact hpNotAncestor hpInUnion

theorem arbitrarily_large_twins_of_movingTerminalSlotAncestorBridge
    (cert : MovingTerminalSlotAncestorBridgeCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_movingTerminalSlotAncestorBridge cert)

/-!
## Direct Unique-Descent Endpoint

This is the same moving-window argument with the certificate record removed.
It is the sharp form of the "unique descents" route:

* for each tail start `B` and eligible exceptional seed `p > B`, a chosen
  terminal event `terminalEvent B p` is produced;
* that event lies in the finite moving window `slots B`;
* if it lies there, the seed `p` is one of the declared ancestors of that
  event.

The ancestor union of a finite window is finite, while Dirichlet gives an
eligible split prime beyond any finite set.  A cofinal exceptional tail would
make such a prime exceptional, forcing it to be both outside and inside the
ancestor union.
-/

theorem no_cofinalExceptionTail_of_uniqueMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    {ancestorsOf : Nat -> Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_records_ancestor :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                p ∈ ancestorsOf B (terminalEvent B p)) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  classical
  intro htail
  rcases htail with ⟨B, tail⟩
  let ancestorUnion := movingSlotAncestorUnion slots ancestorsOf B
  rcases exists_modFiveOnePrime_gt_not_mem_finset
      ancestorUnion (max B threshold) with
    ⟨p, hpgt, hpSeed, hpNotAncestor⟩
  have hpThreshold : threshold < p :=
    lt_of_le_of_lt (le_max_right B threshold) hpgt
  have hBp : B < p :=
    lt_of_le_of_lt (le_max_left B threshold) hpgt
  have hpExceptional : MidpointExceptionalPrime p :=
    tail p hpSeed.1 hBp
  have hSlot : terminalEvent B p ∈ slots B :=
    terminalEvent_in_window B p hBp hpThreshold hpSeed hpExceptional
  have hpInEventAncestors :
      p ∈ ancestorsOf B (terminalEvent B p) :=
    terminalEvent_records_ancestor B p hBp hpThreshold hpSeed hpExceptional
  have hpInUnion : p ∈ ancestorUnion := by
    change p ∈ movingSlotAncestorUnion slots ancestorsOf B
    rw [movingSlotAncestorUnion, Finset.mem_biUnion]
    exact ⟨terminalEvent B p, hSlot, hpInEventAncestors⟩
  exact hpNotAncestor hpInUnion

theorem arbitrarily_large_twins_of_uniqueMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    {ancestorsOf : Nat -> Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_records_ancestor :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                p ∈ ancestorsOf B (terminalEvent B p)) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_uniqueMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_records_ancestor)

/-!
## Direct Injective Moving-Window Endpoint

This is the pure uniqueness version.  It replaces finite ancestor sets by the
more direct condition that the chosen terminal event is injective on eligible
exceptional seeds above the same tail start `B`.

If a cofinal exceptional tail existed, then after `max B threshold` there would
be more eligible exceptional seeds than there are slots in the finite window
`slots B`.  The window-landing theorem maps all of those seeds into `slots B`,
and injectivity makes the image just as large as the seed batch, contradiction.
-/

theorem no_cofinalExceptionTail_of_injectiveMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_injective :
      forall B p q,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                B < q ->
                  threshold < q ->
                    ModFiveOnePrime q ->
                      MidpointExceptionalPrime q ->
                        terminalEvent B p = terminalEvent B q ->
                          p = q) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  classical
  intro htail
  rcases htail with ⟨B, tail⟩
  let N := max B threshold
  let needed := (slots B).card + 1
  rcases exists_modFiveOnePrime_batch_after N needed with
    ⟨seeds, hneeded, hseedMem⟩
  let image : Finset Nat := seeds.image (terminalEvent B)
  have himage_subset : image ⊆ slots B := by
    intro event hevent
    rw [Finset.mem_image] at hevent
    rcases hevent with ⟨p, hpMem, rfl⟩
    have hpData := hseedMem p hpMem
    have hBp : B < p := lt_of_le_of_lt (le_max_left B threshold) hpData.1
    have hpThreshold : threshold < p :=
      lt_of_le_of_lt (le_max_right B threshold) hpData.1
    have hpExceptional : MidpointExceptionalPrime p :=
      tail p hpData.2.1 hBp
    exact terminalEvent_in_window
      B p hBp hpThreshold hpData.2 hpExceptional
  have himage_le : image.card ≤ (slots B).card :=
    Finset.card_le_card himage_subset
  have hinjOn :
      Set.InjOn (terminalEvent B) (fun p => p ∈ seeds) := by
    intro p hpMem q hqMem heq
    have hpData := hseedMem p hpMem
    have hqData := hseedMem q hqMem
    have hBp : B < p := lt_of_le_of_lt (le_max_left B threshold) hpData.1
    have hBq : B < q := lt_of_le_of_lt (le_max_left B threshold) hqData.1
    have hpThreshold : threshold < p :=
      lt_of_le_of_lt (le_max_right B threshold) hpData.1
    have hqThreshold : threshold < q :=
      lt_of_le_of_lt (le_max_right B threshold) hqData.1
    have hpExceptional : MidpointExceptionalPrime p :=
      tail p hpData.2.1 hBp
    have hqExceptional : MidpointExceptionalPrime q :=
      tail q hqData.2.1 hBq
    exact terminalEvent_injective
      B p q hBp hpThreshold hpData.2 hpExceptional
      hBq hqThreshold hqData.2 hqExceptional heq
  have himage_card : image.card = seeds.card := by
    simpa [image] using Finset.card_image_of_injOn (s := seeds) hinjOn
  have htoo_many : (slots B).card < image.card := by
    rw [himage_card]
    exact lt_of_lt_of_le (Nat.lt_succ_self (slots B).card) hneeded
  omega

theorem arbitrarily_large_twins_of_injectiveMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_injective :
      forall B p q,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                B < q ->
                  threshold < q ->
                    ModFiveOnePrime q ->
                      MidpointExceptionalPrime q ->
                        terminalEvent B p = terminalEvent B q ->
                          p = q) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_injectiveMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_injective)

/-!
## Moving-Window Event Pressure Endpoint

This is the endpoint matching the "all valid MP/PM events on the way down
count" interpretation.

`ProducedEvents B p` is the finite set of side-events produced by the recursive
descent from seed `p` while measuring against the moving window attached to
tail start `B`.

No injectivity of seeds is required.  The pressure input is directly about the
number of distinct produced events: after any bound, a finite batch of eligible
seeds produces more distinct events than there are slots in `slots B`.  Under a
cofinal exceptional tail, all those eligible seeds are exceptional, and the
landing theorem puts every produced event into the finite slot set, impossible.
-/

structure MovingWindowEventPressureCertificate where
  threshold : Nat
  slots : Nat -> Finset Nat
  ProducedEvents : Nat -> Nat -> Finset Nat
  distinct_event_pressure :
    forall B N,
      exists seeds : Finset Nat,
        (slots B).card < (seeds.biUnion (ProducedEvents B)).card /\
          forall p, p ∈ seeds ->
            N < p /\ threshold < p /\ ModFiveOnePrime p
  produced_events_land_in_window :
    forall B p event,
      B < p ->
        threshold < p ->
          ModFiveOnePrime p ->
            MidpointExceptionalPrime p ->
              event ∈ ProducedEvents B p ->
                event ∈ slots B

/--
Small-batch specialization of `MovingWindowEventPressureCertificate`.

The current audits suggest the useful deterministic target is often a pair
of consecutive or nearby eligible split seeds.  This structure exposes that
surface directly: after any lower bound, find two eligible seeds whose
distinct produced-event union already overflows the moving slot set.
-/
structure PairEventPressureCertificate where
  threshold : Nat
  slots : Nat -> Finset Nat
  ProducedEvents : Nat -> Nat -> Finset Nat
  pair_event_pressure :
    forall B N,
      exists p q : Nat,
        p < q /\
          N < p /\
            threshold < p /\
              threshold < q /\
                ModFiveOnePrime p /\
                  ModFiveOnePrime q /\
                    (slots B).card <
                      (({p, q} : Finset Nat).biUnion (ProducedEvents B)).card
  produced_events_land_in_window :
    forall B p event,
      B < p ->
        threshold < p ->
          ModFiveOnePrime p ->
            MidpointExceptionalPrime p ->
              event ∈ ProducedEvents B p ->
                event ∈ slots B

def PairEventPressureCertificate.toMovingWindowEventPressure
    (cert : PairEventPressureCertificate) :
    MovingWindowEventPressureCertificate where
  threshold := cert.threshold
  slots := cert.slots
  ProducedEvents := cert.ProducedEvents
  distinct_event_pressure := by
    intro B N
    rcases cert.pair_event_pressure B N with
      ⟨p, q, hpq, hNp, hpThreshold, hqThreshold, hpSeed, hqSeed, hpressure⟩
    refine ⟨({p, q} : Finset Nat), hpressure, ?_⟩
    intro r hr
    rw [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨hNp, hpThreshold, hpSeed⟩
    · exact ⟨lt_trans hNp hpq, hqThreshold, hqSeed⟩
  produced_events_land_in_window := cert.produced_events_land_in_window

theorem no_cofinalExceptionTail_of_movingWindowEventPressure
    (cert : MovingWindowEventPressureCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) := by
  classical
  intro htail
  rcases htail with ⟨B, tail⟩
  rcases cert.distinct_event_pressure B B with
    ⟨seeds, htooMany, hseedMem⟩
  let producedUnion : Finset Nat :=
    seeds.biUnion (cert.ProducedEvents B)
  have hsubset : producedUnion ⊆ cert.slots B := by
    intro event hevent
    change event ∈ seeds.biUnion (cert.ProducedEvents B) at hevent
    rw [Finset.mem_biUnion] at hevent
    rcases hevent with ⟨p, hpMem, heventMem⟩
    have hpData := hseedMem p hpMem
    have hBp : B < p := hpData.1
    have hpThreshold : cert.threshold < p := hpData.2.1
    have hpSeed : ModFiveOnePrime p := hpData.2.2
    have hpExceptional : MidpointExceptionalPrime p :=
      tail p hpSeed.1 hBp
    exact cert.produced_events_land_in_window
      B p event hBp hpThreshold hpSeed hpExceptional heventMem
  have hle : producedUnion.card ≤ (cert.slots B).card :=
    Finset.card_le_card hsubset
  have hgt : (cert.slots B).card < producedUnion.card := by
    change (cert.slots B).card < (seeds.biUnion (cert.ProducedEvents B)).card
    exact htooMany
  omega

theorem arbitrarily_large_twins_of_movingWindowEventPressure
    (cert : MovingWindowEventPressureCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_movingWindowEventPressure cert)

theorem no_cofinalExceptionTail_of_pairEventPressure
    (cert : PairEventPressureCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_movingWindowEventPressure
    cert.toMovingWindowEventPressure

theorem arbitrarily_large_twins_of_pairEventPressure
    (cert : PairEventPressureCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail_of_pairEventPressure cert)

end TwinPrimeCertificate
