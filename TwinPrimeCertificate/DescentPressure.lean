import TwinPrimeCertificate.Core

/-!
# Descent Pressure Counting

This file records the reduced endpoint for the "some positive fraction reaches
the window" strategy.

The theorem is intentionally count-level.  A descent audit may prove that a
fixed fraction of usable starts reaches the target block, while a separate
collision theorem bounds how many successful starts can land on one finite
MP/PM event.  If the successful starts cannot fit under the generated MP/PM
cap, the assumed terminal exception picture is impossible.
-/

namespace TwinPrimeCertificate

/--
A count certificate for a fractional descent transfer.

`successes` is the number of starts whose recursive descent reaches the target
window and contributes to the finite MP/PM event accounting.  The field
`fraction_lower` writes `successes / trials >= num / den` without rationals.
The field `collision_upper` says those successes can fit into at most
`multiplicity` preimages per finite MP/PM event.
-/
structure FractionalDescentPressureCertificate
    (trials cap num den multiplicity : Nat) where
  successes : Nat
  fraction_lower : num * trials <= den * successes
  collision_upper : successes <= multiplicity * cap

/--
If the certified fraction of successful descents is too large to fit into the
finite MP/PM cap under the collision bound, contradiction.
-/
theorem false_of_fractionalDescentPressure
    {trials cap num den multiplicity : Nat}
    (hmargin : den * multiplicity * cap < num * trials)
    (cert :
      FractionalDescentPressureCertificate
        trials cap num den multiplicity) :
    False := by
  have hcollision :
      den * cert.successes <= den * (multiplicity * cap) :=
    Nat.mul_le_mul_left den cert.collision_upper
  have hchain : num * trials <= den * (multiplicity * cap) :=
    le_trans cert.fraction_lower hcollision
  have hreassoc :
      den * (multiplicity * cap) = den * multiplicity * cap := by
    ring
  rw [hreassoc] at hchain
  omega

/--
Generated-cap specialization.

This theorem is useful once an audit supplies:

* `trials` usable starts;
* at least a `num / den` fraction of them reaching the target block;
* collision multiplicity at most `multiplicity` over the generated MP/PM cap.
-/
theorem false_of_generated_fractionalDescentPressure
    {trials num den multiplicity : Nat}
    (hmargin : den * multiplicity * generatedMPPMCard < num * trials)
    (cert :
      FractionalDescentPressureCertificate
        trials generatedMPPMCard num den multiplicity) :
    False :=
  false_of_fractionalDescentPressure hmargin cert

/--
Escape-cap form of the same pressure argument.

If `trials` starts split into successful pressure descents and right-edge
escapes, and the escapes are capped by `escapeCap`, then more than
`cap + escapeCap` trials force pressure above `cap`.
-/
structure EscapeBoundPressureCertificate
    (trials cap escapeCap : Nat) where
  pressure : Nat
  escape : Nat
  cover : trials <= pressure + escape
  pressure_upper : pressure <= cap
  escape_upper : escape <= escapeCap

theorem false_of_escapeBoundPressure
    {trials cap escapeCap : Nat}
    (hmargin : cap + escapeCap < trials)
    (cert : EscapeBoundPressureCertificate trials cap escapeCap) :
    False := by
  have hcoverCap : trials <= cap + escapeCap := by
    exact le_trans cert.cover
      (Nat.add_le_add cert.pressure_upper cert.escape_upper)
  omega

theorem false_of_generated_escapeBoundPressure
    {trials escapeCap : Nat}
    (hmargin : generatedMPPMCard + escapeCap < trials)
    (cert :
      EscapeBoundPressureCertificate
        trials generatedMPPMCard escapeCap) :
    False :=
  false_of_escapeBoundPressure hmargin cert

/--
No-escape finite-fiber freshness.

This is the stripped-down form of the pressure-growth intuition: once a finite
batch of descents all reaches the target window, and each old event can absorb
at most `K` of them, a batch larger than `K * oldEvents.card` must contain a
fresh MP/PM event.
-/
theorem exists_fresh_event_of_no_escape_fiber_bound
    {α β : Type} [DecidableEq α] [DecidableEq β]
    {descents : Finset α} {oldEvents : Finset β} {toEvent : α -> β}
    {K : Nat}
    (fiber_bound :
      ∀ event, event ∈ oldEvents ->
        (descents.filter fun descent => toEvent descent = event).card <= K)
    (hcount : K * oldEvents.card < descents.card) :
    ∃ descent, descent ∈ descents ∧ toEvent descent ∉ oldEvents := by
  classical
  exact exists_new_image_of_fiber_bound
    (newDescents := descents)
    (oldEvents := oldEvents)
    (toEvent := toEvent)
    (K := K)
    fiber_bound
    hcount

/--
Arbitrarily large no-escape batches cannot stay inside a finite old event set
under a uniform finite fiber bound.

This is the form to use when a cofinal exceptional tail supplies finite
prefixes of any requested size.
-/
theorem exists_fresh_event_of_arbitrarily_large_no_escape_batches
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (oldEvents : Finset β) (toEvent : α -> β) (K : Nat)
    (batch :
      ∀ M,
        ∃ descents : Finset α,
          M <= descents.card ∧
            (∀ event, event ∈ oldEvents ->
              (descents.filter fun descent => toEvent descent = event).card <= K)) :
    ∃ descents : Finset α,
      ∃ descent,
        descent ∈ descents ∧ toEvent descent ∉ oldEvents := by
  rcases batch (K * oldEvents.card + 1) with
    ⟨descents, hlarge, hfiber⟩
  have hcount : K * oldEvents.card < descents.card := by
    omega
  rcases exists_new_image_of_fiber_bound
      (newDescents := descents)
      (oldEvents := oldEvents)
      (toEvent := toEvent)
      (K := K)
      hfiber hcount with
    ⟨descent, hmem, hnew⟩
  exact ⟨descents, descent, hmem, hnew⟩

/--
Variable finite-fiber counting over a finite slot set.

If every trial lands in `slots`, and the fiber over each slot `b` is bounded by
the finite number `slotBound b`, then the whole trial batch has size at most
the sum of the slot bounds.
-/
theorem card_le_sum_of_fiber_bounds
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (trials : Finset α) (slots : Finset β) (route : α -> β)
    (slotBound : β -> Nat)
    (route_mem : ∀ a, a ∈ trials -> route a ∈ slots)
    (fiber_bound :
      ∀ b, b ∈ slots ->
        (trials.filter fun a => route a = b).card <= slotBound b) :
    trials.card <= slots.sum slotBound := by
  classical
  let fiber : β -> Finset α := fun b => trials.filter fun a => route a = b
  have hcover : trials ⊆ slots.biUnion fiber := by
    intro a ha
    rw [Finset.mem_biUnion]
    exact ⟨route a, route_mem a ha, by simp [fiber, ha]⟩
  have hcard_cover : trials.card <= (slots.biUnion fiber).card :=
    Finset.card_le_card hcover
  have hbi :
      (slots.biUnion fiber).card <= slots.sum fun b => (fiber b).card :=
    Finset.card_biUnion_le
  have hsum :
      slots.sum (fun b => (fiber b).card) <= slots.sum slotBound := by
    exact Finset.sum_le_sum fun b hb => fiber_bound b hb
  exact le_trans hcard_cover (le_trans hbi hsum)

/--
Finite slots with finite multiplicity cannot absorb arbitrarily large finite
batches.

This is the exact abstract form of the simplified endpoint: once all descents
land in a fixed finite slot set and each slot has a finite fiber cap, there is
a hard total capacity, namely `slots.sum slotBound`.
-/
theorem not_arbitrarily_large_batches_into_finite_slots
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (slots : Finset β) (route : α -> β) (slotBound : β -> Nat) :
    ¬
      (∀ M,
        ∃ descents : Finset α,
          M <= descents.card ∧
            (∀ a, a ∈ descents -> route a ∈ slots) ∧
              (∀ b, b ∈ slots ->
                (descents.filter fun a => route a = b).card <= slotBound b)) := by
  intro hlarge
  rcases hlarge (slots.sum slotBound + 1) with
    ⟨descents, hcard, hroute, hfiber⟩
  have hcap :
      descents.card <= slots.sum slotBound :=
    card_le_sum_of_fiber_bounds
      (trials := descents)
      (slots := slots)
      (route := route)
      (slotBound := slotBound)
      hroute
      hfiber
  omega

/-!
## Exact Lost-Event Recovery

The recovery experiments distinguish two notions:

* recovering the old count, which may happen using different events;
* recovering the exact events lost when the first seed is removed.

The theorem below records the deterministic finite part of the exact-event
version.  If every lost event has a later ancestor seed, then because the lost
set is finite there is one finite extension bound that recovers all lost
events at once.
-/

/--
Finite exact-event recovery from arbitrarily late ancestors.

`ProducedEvents p` is the event set produced by a later seed `p`.  If every
event in the finite `lostEvents` set appears in the produced-event set of some
seed beyond `N`, then there is a finite set of such later seeds whose union
contains all lost events.
-/
theorem exists_finite_recovery_batch_of_lostEvents
    {Event : Type} [DecidableEq Event]
    (lostEvents : Finset Event)
    (ProducedEvents : Nat -> Finset Event)
    (N : Nat)
    (ancestor_after :
      forall event, event ∈ lostEvents ->
        exists p, N < p /\ event ∈ ProducedEvents p) :
    exists seeds : Finset Nat,
      (forall p, p ∈ seeds -> N < p) /\
        lostEvents ⊆ seeds.biUnion ProducedEvents := by
  classical
  let chooseSeed : {event // event ∈ lostEvents} -> Nat :=
    fun event => Classical.choose (ancestor_after event.1 event.2)
  have chooseSeed_spec :
      forall event : {event // event ∈ lostEvents},
        N < chooseSeed event /\ event.1 ∈ ProducedEvents (chooseSeed event) := by
    intro event
    exact Classical.choose_spec (ancestor_after event.1 event.2)
  let seeds : Finset Nat :=
    lostEvents.attach.image fun event => chooseSeed event
  refine ⟨seeds, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨event, _heventMem, rfl⟩
    exact (chooseSeed_spec event).1
  · intro event hevent
    rw [Finset.mem_biUnion]
    let attached : {event // event ∈ lostEvents} := ⟨event, hevent⟩
    refine ⟨chooseSeed attached, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨attached, by simp, rfl⟩
    · exact (chooseSeed_spec attached).2

/--
Prefix-shift exact recovery.

If `oldEvents` is the union before shifting and `shiftedEvents` is the union
after deleting the first seed, then recovering the finite difference
`oldEvents \ shiftedEvents` is enough to restore the exact old event set.
-/
theorem oldEvents_subset_shifted_union_recovery
    {Event : Type} [DecidableEq Event]
    (oldEvents shiftedEvents recoveredEvents : Finset Event)
    (hrecover : oldEvents \ shiftedEvents ⊆ recoveredEvents) :
    oldEvents ⊆ shiftedEvents ∪ recoveredEvents := by
  intro event hevent
  by_cases hshift : event ∈ shiftedEvents
  · exact Finset.mem_union_left recoveredEvents hshift
  · exact Finset.mem_union_right shiftedEvents
      (hrecover (by
        rw [Finset.mem_sdiff]
        exact ⟨hevent, hshift⟩))

/--
Exact recovery as a successor-step object.

This is the abstract version of "scroll `n'` forward until every lost event has
returned."  The only nontrivial input is `ancestor_after`, which is precisely
the mathematical/ascent theorem: each lost event has an ancestor seed after
any requested bound.
-/
theorem exists_exact_recovery_batch_after_shift
    {Event : Type} [DecidableEq Event]
    (oldEvents shiftedEvents : Finset Event)
    (ProducedEvents : Nat -> Finset Event)
    (N : Nat)
    (ancestor_after :
      forall event, event ∈ oldEvents \ shiftedEvents ->
        exists p, N < p /\ event ∈ ProducedEvents p) :
    exists seeds : Finset Nat,
      (forall p, p ∈ seeds -> N < p) /\
        oldEvents ⊆ shiftedEvents ∪ seeds.biUnion ProducedEvents := by
  rcases exists_finite_recovery_batch_of_lostEvents
      (lostEvents := oldEvents \ shiftedEvents)
      (ProducedEvents := ProducedEvents)
      (N := N)
      ancestor_after with
    ⟨seeds, hseedAfter, hrecoversLost⟩
  refine ⟨seeds, hseedAfter, ?_⟩
  exact oldEvents_subset_shifted_union_recovery
    oldEvents shiftedEvents (seeds.biUnion ProducedEvents) hrecoversLost

/-!
## Multiplicity-Two Exact Recovery

This is the weakest exact-recovery principle.  If an event produced before a
tail shift has multiplicity at least two among the old seed prefix, then
deleting one seed cannot delete that event: one of its other producing seeds
remains in the shifted prefix.
-/

/--
If an event has at least two producing seeds in `insert removed shiftedSeeds`,
and the event is produced by `removed`, then it is produced by some shifted
seed.
-/
theorem exists_shifted_seed_of_multiplicity_two
    {Seed Event : Type} [DecidableEq Seed] [DecidableEq Event]
    (ProducedEvents : Seed -> Finset Event)
    (shiftedSeeds : Finset Seed) (removed : Seed) (event : Event)
    (hremoved : event ∈ ProducedEvents removed)
    (hmult :
      2 <=
        (((insert removed shiftedSeeds : Finset Seed).filter
          fun seed => event ∈ ProducedEvents seed).card)) :
    exists seed,
      seed ∈ shiftedSeeds /\ event ∈ ProducedEvents seed := by
  classical
  let fiber : Finset Seed :=
    (insert removed shiftedSeeds).filter fun seed => event ∈ ProducedEvents seed
  have hremovedFiber : removed ∈ fiber := by
    simp [fiber, hremoved]
  by_contra hnone
  have hfiber_subset : fiber ⊆ {removed} := by
    intro seed hseedFiber
    have hseedOld : seed ∈ insert removed shiftedSeeds :=
      (Finset.mem_filter.mp hseedFiber).1
    have hseedEvent : event ∈ ProducedEvents seed :=
      (Finset.mem_filter.mp hseedFiber).2
    rw [Finset.mem_insert] at hseedOld
    rcases hseedOld with hseedRemoved | hseedShifted
    · simp [hseedRemoved]
    · exact False.elim (hnone ⟨seed, hseedShifted, hseedEvent⟩)
  have hcard_le_one : fiber.card <= 1 := by
    have hle : fiber.card <= ({removed} : Finset Seed).card :=
      Finset.card_le_card hfiber_subset
    simpa using hle
  have hcard_ge_two : 2 <= fiber.card := hmult
  omega

/--
Multiplicity-two recovery for a prefix shift.

Let `oldEvents` be generated by `insert removed shiftedSeeds`.  If every event
generated by the removed seed has multiplicity at least two in the old prefix,
then all old events are still present after the shift.
-/
theorem oldEvents_subset_shifted_of_removed_events_multiplicity_two
    {Seed Event : Type} [DecidableEq Seed] [DecidableEq Event]
    (ProducedEvents : Seed -> Finset Event)
    (shiftedSeeds : Finset Seed) (removed : Seed)
    (hmult :
      forall event, event ∈ ProducedEvents removed ->
        2 <=
          (((insert removed shiftedSeeds : Finset Seed).filter
            fun seed => event ∈ ProducedEvents seed).card)) :
    (insert removed shiftedSeeds : Finset Seed).biUnion ProducedEvents ⊆
      shiftedSeeds.biUnion ProducedEvents := by
  classical
  intro event hevent
  rw [Finset.mem_biUnion] at hevent ⊢
  rcases hevent with ⟨seed, hseedOld, hseedEvent⟩
  rw [Finset.mem_insert] at hseedOld
  rcases hseedOld with hseedRemoved | hseedShifted
  · subst seed
    rcases exists_shifted_seed_of_multiplicity_two
        ProducedEvents shiftedSeeds removed event
        hseedEvent (hmult event hseedEvent) with
      ⟨seed', hseed', hevent'⟩
    exact ⟨seed', hseed', hevent'⟩
  · exact ⟨seed, hseedShifted, hseedEvent⟩

/--
Extension form: if later seeds give multiplicity two for every event produced
by the removed seed, then the old prefix is contained in the shifted prefix
plus the later recovery batch.
-/
theorem oldEvents_subset_shifted_union_later_of_multiplicity_two
    {Seed Event : Type} [DecidableEq Seed] [DecidableEq Event]
    (ProducedEvents : Seed -> Finset Event)
    (shiftedSeeds laterSeeds : Finset Seed) (removed : Seed)
    (hmult :
      forall event, event ∈ ProducedEvents removed ->
        2 <=
          (((insert removed (shiftedSeeds ∪ laterSeeds) : Finset Seed).filter
            fun seed => event ∈ ProducedEvents seed).card)) :
    (insert removed shiftedSeeds : Finset Seed).biUnion ProducedEvents ⊆
      shiftedSeeds.biUnion ProducedEvents ∪ laterSeeds.biUnion ProducedEvents := by
  classical
  have hsubset_big :
      (insert removed (shiftedSeeds ∪ laterSeeds) : Finset Seed).biUnion ProducedEvents ⊆
        (shiftedSeeds ∪ laterSeeds).biUnion ProducedEvents :=
    oldEvents_subset_shifted_of_removed_events_multiplicity_two
      ProducedEvents (shiftedSeeds ∪ laterSeeds) removed hmult
  intro event hevent
  have hevent_big :
      event ∈ (insert removed (shiftedSeeds ∪ laterSeeds) : Finset Seed).biUnion ProducedEvents := by
    rw [Finset.mem_biUnion] at hevent ⊢
    rcases hevent with ⟨seed, hseed, hseedEvent⟩
    refine ⟨seed, ?_, hseedEvent⟩
    rw [Finset.mem_insert] at hseed ⊢
    rcases hseed with hremoved | hshifted
    · exact Or.inl hremoved
    · exact Or.inr (Finset.mem_union_left laterSeeds hshifted)
  have hin_unionSeeds :
      event ∈ (shiftedSeeds ∪ laterSeeds).biUnion ProducedEvents :=
    hsubset_big hevent_big
  rw [Finset.mem_biUnion] at hin_unionSeeds
  rcases hin_unionSeeds with ⟨seed, hseed, hseedEvent⟩
  rw [Finset.mem_union] at hseed
  rcases hseed with hshifted | hlater
  · exact Finset.mem_union_left _
      (by
        rw [Finset.mem_biUnion]
        exact ⟨seed, hshifted, hseedEvent⟩)
  · exact Finset.mem_union_right _
      (by
        rw [Finset.mem_biUnion]
        exact ⟨seed, hlater, hseedEvent⟩)

/-!
## Multiplicity Supplies Later Ancestors

The previous theorems say that multiplicity two recovers events once a later
batch is in hand.  The next lemmas isolate the forward implication from a
finite multiplicity certificate to a later ancestor.
-/

/--
If a finite batch after `N` contains at least one producer of `event`, then
`event` has a later ancestor.
-/
theorem exists_later_ancestor_of_positive_multiplicity
    {Event : Type} [DecidableEq Event]
    (ProducedEvents : Nat -> Finset Event)
    (event : Event) (N : Nat) (seeds : Finset Nat)
    (seeds_after : forall p, p ∈ seeds -> N < p)
    (hpositive :
      0 <
        (seeds.filter fun p => event ∈ ProducedEvents p).card) :
    exists p, N < p /\ event ∈ ProducedEvents p := by
  classical
  rcases Finset.card_pos.mp hpositive with ⟨p, hp⟩
  have hpSeed : p ∈ seeds := (Finset.mem_filter.mp hp).1
  have hpEvent : event ∈ ProducedEvents p := (Finset.mem_filter.mp hp).2
  exact ⟨p, seeds_after p hpSeed, hpEvent⟩

/--
Multiplicity at least two is more than enough to produce a later ancestor.
-/
theorem exists_later_ancestor_of_multiplicity_two
    {Event : Type} [DecidableEq Event]
    (ProducedEvents : Nat -> Finset Event)
    (event : Event) (N : Nat) (seeds : Finset Nat)
    (seeds_after : forall p, p ∈ seeds -> N < p)
    (hmult :
      2 <=
        (seeds.filter fun p => event ∈ ProducedEvents p).card) :
    exists p, N < p /\ event ∈ ProducedEvents p := by
  exact exists_later_ancestor_of_positive_multiplicity
    ProducedEvents event N seeds seeds_after (by omega)

/--
Eligible multiplicity supplies an eligible later ancestor.

This is the exact local statement needed by the shifted-tail proof:
for one event, a finite after-`N` batch of eligible split seeds with
multiplicity at least two yields a later eligible ancestor for that event.
-/
theorem exists_later_eligible_ancestor_of_multiplicity_two
    {Event : Type} [DecidableEq Event]
    (ProducedEvents : Nat -> Finset Event)
    (event : Event) (N : Nat) (seeds : Finset Nat)
    (seeds_after :
      forall p, p ∈ seeds -> N < p)
    (seeds_eligible :
      forall p, p ∈ seeds -> ModFiveOnePrime p)
    (hmult :
      2 <=
        (seeds.filter fun p => event ∈ ProducedEvents p).card) :
    exists p, N < p /\ ModFiveOnePrime p /\ event ∈ ProducedEvents p := by
  classical
  have hpositive :
      0 < (seeds.filter fun p => event ∈ ProducedEvents p).card := by
    omega
  rcases Finset.card_pos.mp hpositive with ⟨p, hp⟩
  have hpSeed : p ∈ seeds := (Finset.mem_filter.mp hp).1
  have hpEvent : event ∈ ProducedEvents p := (Finset.mem_filter.mp hp).2
  exact ⟨p, seeds_after p hpSeed, seeds_eligible p hpSeed, hpEvent⟩

/--
Finite lost-event family version.

If every lost event has, after any bound `N`, a finite eligible seed batch in
which it appears with multiplicity at least two, then every lost event has an
arbitrarily late eligible split-prime ancestor.
-/
theorem lostEvents_have_later_eligible_ancestors_of_multiplicity_two
    {Event : Type} [DecidableEq Event]
    (lostEvents : Finset Event)
    (ProducedEvents : Nat -> Finset Event)
    (multiplicity_two_after :
      forall N event, event ∈ lostEvents ->
        exists seeds : Finset Nat,
          (forall p, p ∈ seeds -> N < p) /\
            (forall p, p ∈ seeds -> ModFiveOnePrime p) /\
              2 <=
                (seeds.filter fun p => event ∈ ProducedEvents p).card) :
    forall N event, event ∈ lostEvents ->
      exists p, N < p /\ ModFiveOnePrime p /\ event ∈ ProducedEvents p := by
  intro N event hevent
  rcases multiplicity_two_after N event hevent with
    ⟨seeds, hafter, heligible, hmult⟩
  exact exists_later_eligible_ancestor_of_multiplicity_two
    ProducedEvents event N seeds hafter heligible hmult

/--
Exact recovery with eligible later ancestors.

This packages the whole forward chain:

1. multiplicity-two batches give arbitrarily late eligible ancestors;
2. arbitrarily late ancestors give a finite recovery batch;
3. the shifted prefix plus that finite batch contains the old event set.
-/
theorem exists_exact_eligible_recovery_batch_after_shift
    {Event : Type} [DecidableEq Event]
    (oldEvents shiftedEvents : Finset Event)
    (ProducedEvents : Nat -> Finset Event)
    (N : Nat)
    (multiplicity_two_after :
      forall N event, event ∈ oldEvents \ shiftedEvents ->
        exists seeds : Finset Nat,
          (forall p, p ∈ seeds -> N < p) /\
            (forall p, p ∈ seeds -> ModFiveOnePrime p) /\
              2 <=
                (seeds.filter fun p => event ∈ ProducedEvents p).card) :
    exists seeds : Finset Nat,
      (forall p, p ∈ seeds -> N < p) /\
        (forall p, p ∈ seeds -> ModFiveOnePrime p) /\
          oldEvents ⊆ shiftedEvents ∪ seeds.biUnion ProducedEvents := by
  classical
  have ancestor_after :
      forall event, event ∈ oldEvents \ shiftedEvents ->
        exists p, N < p /\ event ∈ ProducedEvents p := by
    intro event hevent
    rcases lostEvents_have_later_eligible_ancestors_of_multiplicity_two
        (lostEvents := oldEvents \ shiftedEvents)
        (ProducedEvents := ProducedEvents)
        multiplicity_two_after N event hevent with
      ⟨p, hpAfter, _hpEligible, hpEvent⟩
    exact ⟨p, hpAfter, hpEvent⟩
  rcases exists_exact_recovery_batch_after_shift
      oldEvents shiftedEvents ProducedEvents N ancestor_after with
    ⟨seeds, hafter, hsubset⟩
  -- Rechoose the recovery batch with eligibility retained.
  let chooseSeed : {event // event ∈ oldEvents \ shiftedEvents} -> Nat :=
    fun event =>
      Classical.choose
        (lostEvents_have_later_eligible_ancestors_of_multiplicity_two
          (lostEvents := oldEvents \ shiftedEvents)
          (ProducedEvents := ProducedEvents)
          multiplicity_two_after N event.1 event.2)
  have chooseSeed_spec :
      forall event : {event // event ∈ oldEvents \ shiftedEvents},
        N < chooseSeed event /\
          ModFiveOnePrime (chooseSeed event) /\
            event.1 ∈ ProducedEvents (chooseSeed event) := by
    intro event
    exact Classical.choose_spec
      (lostEvents_have_later_eligible_ancestors_of_multiplicity_two
        (lostEvents := oldEvents \ shiftedEvents)
        (ProducedEvents := ProducedEvents)
        multiplicity_two_after N event.1 event.2)
  let eligibleSeeds : Finset Nat :=
    (oldEvents \ shiftedEvents).attach.image fun event => chooseSeed event
  refine ⟨eligibleSeeds, ?_, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨event, _heventMem, rfl⟩
    exact (chooseSeed_spec event).1
  · intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨event, _heventMem, rfl⟩
    exact (chooseSeed_spec event).2.1
  · exact oldEvents_subset_shifted_union_recovery
      oldEvents shiftedEvents (eligibleSeeds.biUnion ProducedEvents)
      (by
        intro event hevent
        rw [Finset.mem_biUnion]
        let attached : {event // event ∈ oldEvents \ shiftedEvents} :=
          ⟨event, hevent⟩
        refine ⟨chooseSeed attached, ?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨attached, by simp, rfl⟩
        · exact (chooseSeed_spec attached).2.2)

end TwinPrimeCertificate
