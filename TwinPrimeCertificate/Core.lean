import Mathlib.Tactic
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Minimal Twin-Prime Endpoint Core

This file contains only the Lean-checked endpoint logic.

The endpoint logic is parameterized by one concrete no-tail theorem:

```
Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B)
```

From that single obstruction, Lean proves arbitrarily large
twin primes by the following elementary chain:

* bounded twin-prime midpoints give a cofinal tail of exceptional primes;
* the supplied pressure/realization theorem rules out such a cofinal tail;
* twin midpoints are unbounded;
* twin primes are arbitrarily large.
-/

namespace TwinPrimeCertificate

def lastObservedException : Nat := 127

def observedVerifiedTo : Nat := 1000000000

def certificateVerifiedTo : Nat := 191264

def certificateFirstSplitPrime : Nat := 191281

def certificatePrefixStart : Nat := certificateFirstSplitPrime

def certificatePrefixEnd : Nat := certificateFirstSplitPrime

def generatedMPPMCard : Nat := 95568

/--
The residue class used for the generated quadratic rows.

The C++ generator accepts all primes for which `5` is a quadratic residue.  A
particularly simple infinite subfamily is `p ≡ 1 [MOD 5]`, supplied by
mathlib's `Nat.exists_prime_gt_modEq_one`.
-/
def ModFiveOnePrime (p : Nat) : Prop :=
  Nat.Prime p ∧ p ≡ 1 [MOD 5]

theorem exists_modFiveOnePrime_gt (N : Nat) :
    ∃ p, N < p ∧ ModFiveOnePrime p := by
  rcases Nat.exists_prime_gt_modEq_one (k := 5) N (by norm_num) with
    ⟨p, hpprime, hpgt, hpmod⟩
  exact ⟨p, hpgt, hpprime, hpmod⟩

/--
No finite set of candidate ancestors can contain all sufficiently large usable
split primes.

This is the elementary "finite traps cannot catch the tail" fact.  The proof
uses only Dirichlet's theorem in the `p ≡ 1 [MOD 5]` class, as exposed by
mathlib through `Nat.exists_prime_gt_modEq_one`.
-/
theorem exists_modFiveOnePrime_gt_not_mem_finset
    (ancestors : Finset Nat) (N : Nat) :
    ∃ p, N < p ∧ ModFiveOnePrime p ∧ p ∉ ancestors := by
  classical
  by_cases hnonempty : ancestors.Nonempty
  · let bound := max N (ancestors.max' hnonempty)
    rcases exists_modFiveOnePrime_gt bound with ⟨p, hpgt, hpseed⟩
    refine ⟨p, ?_, hpseed, ?_⟩
    · exact lt_of_le_of_lt (le_max_left N (ancestors.max' hnonempty)) hpgt
    · intro hmem
      have hple : p ≤ ancestors.max' hnonempty :=
        Finset.le_max' ancestors p hmem
      have hmaxlt : ancestors.max' hnonempty < p :=
        lt_of_le_of_lt
          (le_max_right N (ancestors.max' hnonempty)) hpgt
      omega
  · rcases exists_modFiveOnePrime_gt N with ⟨p, hpgt, hpseed⟩
    refine ⟨p, hpgt, hpseed, ?_⟩
    intro hmem
    exact hnonempty ⟨p, hmem⟩

/--
Equivalently, a finite ancestor set cannot contain a cofinal tail of all usable
split primes.
-/
theorem not_cofinal_modFiveOnePrimes_subset_finset
    (ancestors : Finset Nat) :
    ¬ ∃ B,
      ∀ p, B < p -> ModFiveOnePrime p -> p ∈ ancestors := by
  intro h
  rcases h with ⟨B, hB⟩
  rcases exists_modFiveOnePrime_gt_not_mem_finset ancestors B with
    ⟨p, hpgt, hpseed, hpnot⟩
  exact hpnot (hB p hpgt hpseed)

structure ObservedExceptionGap where
  lastException : Nat
  verifiedTo : Nat
  hlt : lastException < verifiedTo

def ObservedExceptionGap.size (gap : ObservedExceptionGap) : Nat :=
  gap.verifiedTo - gap.lastException

def observedExceptionGap : ObservedExceptionGap where
  lastException := lastObservedException
  verifiedTo := observedVerifiedTo
  hlt := by
    norm_num [lastObservedException, observedVerifiedTo]

def certificateExceptionGap : ObservedExceptionGap where
  lastException := lastObservedException
  verifiedTo := certificateVerifiedTo
  hlt := by
    norm_num [lastObservedException, certificateVerifiedTo]

theorem certificateVerifiedTo_le_observed :
    certificateExceptionGap.verifiedTo <= observedExceptionGap.verifiedTo := by
  norm_num [certificateExceptionGap, observedExceptionGap,
    certificateVerifiedTo, observedVerifiedTo]

/-- The first exceptional prime after a verified no-exception gap. -/
structure FirstExceptionAfterGap
    (Exception : Nat -> Prop)
    (gap : ObservedExceptionGap) where
  r : Nat
  hr : Nat.Prime r
  hafter : gap.verifiedTo < r
  exception : Exception r
  first_after_gap :
    forall s,
      Nat.Prime s ->
        gap.verifiedTo < s ->
          s < r ->
            Not (Exception s)

/-- A first exception after `lastObservedException`, independent of a chosen gap. -/
structure FirstExceptionAfterLastObserved
    (Exception : Nat -> Prop) where
  r : Nat
  hr : Nat.Prime r
  hafterLast : lastObservedException < r
  exception : Exception r
  first_after_last :
    forall s,
      Nat.Prime s ->
        lastObservedException < s ->
          s < r ->
            Not (Exception s)

/--
Certificate predicate: no prime in `(lastObservedException, checkedTo]`
is exceptional.
-/
def ExceptionFreeUpTo
    (Exception : Nat -> Prop)
    (checkedTo : Nat) : Prop :=
  forall r,
    Nat.Prime r ->
      lastObservedException < r ->
        r <= checkedTo ->
          Not (Exception r)

theorem firstExceptionAfterLast_occurs_after_of_exceptionFreeUpTo
    {Exception : Nat -> Prop}
    {checkedTo : Nat}
    (free : ExceptionFreeUpTo Exception checkedTo)
    (firstException : FirstExceptionAfterLastObserved Exception) :
    checkedTo < firstException.r := by
  by_contra hnot
  exact free firstException.r firstException.hr firstException.hafterLast
    (le_of_not_gt hnot) firstException.exception

theorem firstExceptionAfterLast_occurs_after_certificateThreshold_of_exceptionFreeUpTo
    {Exception : Nat -> Prop}
    (free : ExceptionFreeUpTo Exception certificateVerifiedTo)
    (firstException : FirstExceptionAfterLastObserved Exception) :
    certificateVerifiedTo < firstException.r :=
  firstExceptionAfterLast_occurs_after_of_exceptionFreeUpTo free firstException

/-- After `B`, every prime is exceptional. -/
def CofinalExceptionTail (Exception : Nat -> Prop) (B : Nat) : Prop :=
  forall r, Nat.Prime r -> B < r -> Exception r

theorem cofinalTail_forces_seed
    {Exception : Nat -> Prop} {B seed : Nat}
    (tail : CofinalExceptionTail Exception B)
    (hseed : Nat.Prime seed)
    (hBseed : B < seed) :
    Exception seed :=
  tail seed hseed hBseed

theorem certificateFirstSplitPrime_prime :
    Nat.Prime certificateFirstSplitPrime := by
  native_decide

theorem cofinalTail_forces_certificateFirstSplitPrime
    {B : Nat}
    (tail : CofinalExceptionTail MidpointExceptionalPrime B)
    (hBseed : B < certificateFirstSplitPrime) :
    MidpointExceptionalPrime certificateFirstSplitPrime :=
  cofinalTail_forces_seed tail certificateFirstSplitPrime_prime hBseed

/--
A cofinal exceptional tail contains arbitrarily large primes in the generated
`p ≡ 1 [MOD 5]` seed class.

This is the formal "fresh exceptional starts never run out" input needed by
the recursive-pressure picture.
-/
theorem cofinalTail_has_modFiveOne_exceptional_seed_after
    {B N : Nat}
    (tail : CofinalExceptionTail MidpointExceptionalPrime B) :
    ∃ p,
      N < p ∧
        ModFiveOnePrime p ∧
          MidpointExceptionalPrime p := by
  rcases exists_modFiveOnePrime_gt (max B N) with
    ⟨p, hpgt, hpseed⟩
  have hBp : B < p := lt_of_le_of_lt (le_max_left B N) hpgt
  have hNp : N < p := lt_of_le_of_lt (le_max_right B N) hpgt
  exact ⟨p, hNp, hpseed, tail p hpseed.1 hBp⟩

/-- A cofinal tail starting after `B` is already contradictory. -/
def CofinalTailContradicts (Exception : Nat -> Prop) (B : Nat) : Prop :=
  CofinalExceptionTail Exception B -> False

theorem cofinalTail_mono_threshold
    {Exception : Nat -> Prop} {B C : Nat}
    (hBC : B <= C)
    (tail : CofinalExceptionTail Exception B) :
    CofinalExceptionTail Exception C := by
  intro r hr hCr
  exact tail r hr (lt_of_le_of_lt hBC hCr)

theorem cofinalTailContradicts_mono_backward
    {Exception : Nat -> Prop} {B C : Nat}
    (hBC : B <= C)
    (hnoC : CofinalTailContradicts Exception C) :
    CofinalTailContradicts Exception B := by
  intro tailB
  exact hnoC (cofinalTail_mono_threshold hBC tailB)

/--
A finite exceptional prefix from `(B, C]`.

Together with a cofinal tail after `C`, this reconstructs a cofinal tail after
`B`.  This is the precise finite-prefix bookkeeping used by the shifted-tail
argument.
-/
def ExceptionPrefix
    (Exception : Nat -> Prop)
    (B C : Nat) : Prop :=
  forall r, Nat.Prime r -> B < r -> r <= C -> Exception r

theorem cofinalTail_of_exceptionPrefix_of_cofinalTail
    {Exception : Nat -> Prop} {B C : Nat}
    (pref : ExceptionPrefix Exception B C)
    (tailC : CofinalExceptionTail Exception C) :
    CofinalExceptionTail Exception B := by
  intro r hr hBr
  by_cases hrC : r <= C
  · exact pref r hr hBr hrC
  · exact tailC r hr (lt_of_not_ge hrC)

theorem cofinalTailContradicts_of_exceptionPrefix
    {Exception : Nat -> Prop} {B C : Nat}
    (hnoB : CofinalTailContradicts Exception B)
    (pref : ExceptionPrefix Exception B C) :
    CofinalTailContradicts Exception C := by
  intro tailC
  exact hnoB (cofinalTail_of_exceptionPrefix_of_cofinalTail pref tailC)

/--
Successor recovery with finite prefix lengthening.

To prove that a tail beginning after `B + 1` is contradictory, it is enough to
recover the lost finite prefix up to some later bound `C`.  The exact length is
irrelevant: once `(B, C]` is exceptional, any tail after `B + 1` restricts to a
tail after `C`, and the prefix reconstructs a tail after `B`.
-/
theorem cofinalTailContradicts_successor_of_finite_prefix
    {Exception : Nat -> Prop} {B C : Nat}
    (hnoB : CofinalTailContradicts Exception B)
    (hBC : B + 1 <= C)
    (pref : ExceptionPrefix Exception B C) :
    CofinalTailContradicts Exception (B + 1) := by
  intro tailSucc
  have hnoC : CofinalTailContradicts Exception C :=
    cofinalTailContradicts_of_exceptionPrefix hnoB pref
  exact hnoC (cofinalTail_mono_threshold hBC tailSucc)

theorem cofinalTailContradicts_successor_of_exists_finite_prefix
    {Exception : Nat -> Prop} {B : Nat}
    (hnoB : CofinalTailContradicts Exception B)
    (hrecover :
      exists C, B + 1 <= C /\ ExceptionPrefix Exception B C) :
    CofinalTailContradicts Exception (B + 1) := by
  rcases hrecover with ⟨C, hBC, pref⟩
  exact cofinalTailContradicts_successor_of_finite_prefix hnoB hBC pref

theorem cofinalTailContradicts_successor_of_succ_exception
    {Exception : Nat -> Prop} {B : Nat}
    (hnoB : CofinalTailContradicts Exception B)
    (hsucc : Nat.Prime (B + 1) -> Exception (B + 1)) :
    CofinalTailContradicts Exception (B + 1) := by
  refine cofinalTailContradicts_of_exceptionPrefix hnoB ?_
  intro r hr hBr hrle
  have hr_eq : r = B + 1 := by omega
  subst r
  exact hsucc hr

/--
Eventual finite-prefix count recovery.

If a natural-valued prefix count can always be increased after some finite
lengthening whenever it is still at most `cap`, then some finite lengthening
pushes the count above `cap`.

This is the abstract counting core of the shifted-tail pressure argument.  It
does not know what the counted objects are; it only records that repeated
finite recovery cannot stay below a finite cap forever.
-/
theorem exists_count_exceeds_of_eventual_increment
    {count : Nat -> Nat} {start cap : Nat}
    (hinc :
      ∀ n, start <= n -> count n <= cap ->
        ∃ m, n <= m /\ count n < count m) :
    ∃ m, start <= m /\ cap < count m := by
  by_contra hnone
  have hleall : ∀ m, start <= m -> count m <= cap := by
    intro m hm
    by_contra hnot
    have hgt : cap < count m := by omega
    exact hnone ⟨m, hm, hgt⟩
  have hcount : ∀ k, ∃ n, start <= n /\ count start + k <= count n := by
    intro k
    induction k with
    | zero =>
        exact ⟨start, le_rfl, by omega⟩
    | succ k ih =>
      rcases ih with ⟨n, hnstart, hncount⟩
      rcases hinc n hnstart (hleall n hnstart) with ⟨m, hnm, hlt⟩
      exact ⟨m, le_trans hnstart hnm, by omega⟩
  rcases hcount (cap + 1) with ⟨m, hmstart, hmcount⟩
  have hbig : cap < count m := by
    omega
  exact hnone ⟨m, hmstart, hbig⟩

/--
If a finite family has more distinct images than an old event set has
elements, then at least one member maps to a genuinely new event.

This is the pigeonhole core needed for shifted-tail freshness.  It deliberately
counts distinct images, not raw descents: many descents may collide at the same
terminal MP/PM event.
-/
theorem exists_new_image_of_card_lt_image
    {α β : Type} [DecidableEq β]
    {newDescents : Finset α} {oldEvents : Finset β} {toEvent : α -> β}
    (hcard : oldEvents.card < (newDescents.image toEvent).card) :
    ∃ descent, descent ∈ newDescents ∧ toEvent descent ∉ oldEvents := by
  by_contra hnone
  have hsubset : newDescents.image toEvent ⊆ oldEvents := by
    intro event hevent
    rcases Finset.mem_image.mp hevent with ⟨descent, hdescent, rfl⟩
    by_contra hold
    exact hnone ⟨descent, hdescent, hold⟩
  have hle : (newDescents.image toEvent).card <= oldEvents.card :=
    Finset.card_le_card hsubset
  omega

/--
Generic bounded-fiber counting.

If every slot receives at most `K` selected trials, then the number of trials
is at most `K * slots.card`.
-/
theorem card_le_mul_of_fiber_bound
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (trials : Finset α) (slots : Finset β) (route : α -> β)
    {K : Nat}
    (route_mem : ∀ a, a ∈ trials -> route a ∈ slots)
    (fiber_bound :
      ∀ b, b ∈ slots ->
        (trials.filter fun a => route a = b).card <= K) :
    trials.card <= K * slots.card := by
  classical
  let fiber : β -> Finset α := fun b => trials.filter fun a => route a = b
  have hcover : trials ⊆ slots.biUnion fiber := by
    intro a ha
    rw [Finset.mem_biUnion]
    refine ⟨route a, route_mem a ha, ?_⟩
    simp [fiber, ha]
  have hcard_cover : trials.card <= (slots.biUnion fiber).card :=
    Finset.card_le_card hcover
  have hbi :
      (slots.biUnion fiber).card <= slots.sum fun b => (fiber b).card :=
    Finset.card_biUnion_le
  have hsum :
      slots.sum (fun b => (fiber b).card) <= slots.sum fun _b => K := by
    exact Finset.sum_le_sum fun b hb => fiber_bound b hb
  have hsumK : slots.sum (fun _b => K) = slots.card * K := by
    simp [Nat.mul_comm]
  calc
    trials.card <= (slots.biUnion fiber).card := hcard_cover
    _ <= slots.sum fun b => (fiber b).card := hbi
    _ <= slots.sum fun _b => K := hsum
    _ = slots.card * K := hsumK
    _ = K * slots.card := by rw [Nat.mul_comm]

/--
Bounded-collision freshness.

If every old event can absorb at most `K` new descents, but the new finite
prefix contains more than `K * oldEvents.card` descents, then some descent
lands at a terminal event that was not already recorded.
-/
theorem exists_new_image_of_fiber_bound
    {α β : Type} [DecidableEq α] [DecidableEq β]
    {newDescents : Finset α} {oldEvents : Finset β} {toEvent : α -> β}
    {K : Nat}
    (fiber_bound :
      ∀ event, event ∈ oldEvents ->
        (newDescents.filter fun descent => toEvent descent = event).card <= K)
    (hcount : K * oldEvents.card < newDescents.card) :
    ∃ descent, descent ∈ newDescents ∧ toEvent descent ∉ oldEvents := by
  by_contra hnone
  have route_mem :
      ∀ descent, descent ∈ newDescents -> toEvent descent ∈ oldEvents := by
    intro descent hdescent
    by_contra hnot
    exact hnone ⟨descent, hdescent, hnot⟩
  have hle : newDescents.card <= K * oldEvents.card :=
    card_le_mul_of_fiber_bound
      (trials := newDescents)
      (slots := oldEvents)
      (route := toEvent)
      (K := K)
      route_mem
      fiber_bound
  omega

/--
Freshness with escapes.

If a finite prefix has more descents than can be explained by the declared
escape budget plus `K` collisions over each old event, then at least one
non-escape descent lands at a genuinely new event.

This is the counting form of the intended pressure-growth argument:

```
total descents > escapes + K * old events
  => fresh MP/PM event.
```
-/
theorem exists_fresh_event_of_escape_and_fiber_bounds
    {α β : Type} [DecidableEq α] [DecidableEq β]
    {descents : Finset α} {oldEvents : Finset β} {toEvent : α -> β}
    (isEscape : α -> Prop) [DecidablePred isEscape]
    {K escapeCap : Nat}
    (escape_bound :
      (descents.filter fun descent => isEscape descent).card <= escapeCap)
    (fiber_bound :
      ∀ event, event ∈ oldEvents ->
        ((descents.filter fun descent => ¬ isEscape descent).filter
          fun descent => toEvent descent = event).card <= K)
    (hcount : escapeCap + K * oldEvents.card < descents.card) :
    ∃ descent,
      descent ∈ descents ∧
        ¬ isEscape descent ∧
          toEvent descent ∉ oldEvents := by
  classical
  let escapes : Finset α := descents.filter fun descent => isEscape descent
  let good : Finset α := descents.filter fun descent => ¬ isEscape descent
  by_contra hnone
  have route_mem :
      ∀ descent, descent ∈ good -> toEvent descent ∈ oldEvents := by
    intro descent hdescent
    by_contra hnot
    have hdesc : descent ∈ descents := by
      exact (Finset.mem_filter.mp hdescent).1
    have hgood : ¬ isEscape descent := by
      exact (Finset.mem_filter.mp hdescent).2
    exact hnone ⟨descent, hdesc, hgood, hnot⟩
  have hgood_le : good.card <= K * oldEvents.card := by
    exact card_le_mul_of_fiber_bound
      (trials := good)
      (slots := oldEvents)
      (route := toEvent)
      (K := K)
      route_mem
      (by
        intro event hevent
        simpa [good] using fiber_bound event hevent)
  have hesc_le : escapes.card <= escapeCap := by
    simpa [escapes] using escape_bound
  have hcover : descents ⊆ escapes ∪ good := by
    intro descent hdescent
    by_cases hesc : isEscape descent
    · simp [escapes, good, hdescent, hesc]
    · simp [escapes, good, hdescent, hesc]
  have hcard_union :
      descents.card <= escapes.card + good.card := by
    exact le_trans (Finset.card_le_card hcover) (Finset.card_union_le escapes good)
  have hle :
      descents.card <= escapeCap + K * oldEvents.card :=
    le_trans hcard_union (Nat.add_le_add hesc_le hgood_le)
  exact (not_lt_of_ge hle) hcount

/--
Fiber bounds multiply under route composition.

This is the abstract version of the "K <= 2 per routed step" bookkeeping:
if each intermediate node has at most `K₁` incoming selected descents, and
each terminal event has at most `K₂` incoming intermediate nodes, then each
terminal event has at most `K₁ * K₂` incoming selected descents under the
composite route.  Iterating this theorem gives the expected `2 ^ depth`
collision budget for a depth-bounded descent certificate.
-/
theorem composite_fiber_bound
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (domain : Finset α) (middle : Finset β)
    (route₁ : α -> β) (route₂ : β -> γ)
    {K₁ K₂ : Nat}
    (route₁_mem : ∀ a, a ∈ domain -> route₁ a ∈ middle)
    (fiber₁_bound :
      ∀ b, b ∈ middle ->
        (domain.filter fun a => route₁ a = b).card <= K₁)
    (fiber₂_bound :
      ∀ c,
        (middle.filter fun b => route₂ b = c).card <= K₂)
    (c : γ) :
    (domain.filter fun a => route₂ (route₁ a) = c).card <= K₁ * K₂ := by
  classical
  let middleForC : Finset β := middle.filter fun b => route₂ b = c
  let fiber₁ : β -> Finset α := fun b => domain.filter fun a => route₁ a = b
  have hcover :
      (domain.filter fun a => route₂ (route₁ a) = c) ⊆
        middleForC.biUnion fiber₁ := by
    intro a ha
    have hadomain : a ∈ domain := (Finset.mem_filter.mp ha).1
    have hroute₂ : route₂ (route₁ a) = c := (Finset.mem_filter.mp ha).2
    have hmiddle : route₁ a ∈ middle := route₁_mem a hadomain
    rw [Finset.mem_biUnion]
    refine ⟨route₁ a, ?_, ?_⟩
    · simp [middleForC, hmiddle, hroute₂]
    · simp [fiber₁, hadomain]
  have hcard_cover :
      (domain.filter fun a => route₂ (route₁ a) = c).card <=
        (middleForC.biUnion fiber₁).card :=
    Finset.card_le_card hcover
  have hbi :
      (middleForC.biUnion fiber₁).card <=
        middleForC.sum fun b => (fiber₁ b).card :=
    Finset.card_biUnion_le
  have hsum_bound :
      middleForC.sum (fun b => (fiber₁ b).card) <=
        middleForC.sum fun _b => K₁ := by
    refine Finset.sum_le_sum ?_
    intro b hb
    have hmiddle : b ∈ middle := (Finset.mem_filter.mp hb).1
    exact fiber₁_bound b hmiddle
  have hsumK :
      middleForC.sum (fun _b => K₁) = middleForC.card * K₁ := by
    simp [Nat.mul_comm]
  have hmiddle_card : middleForC.card <= K₂ := by
    simpa [middleForC] using fiber₂_bound c
  calc
    (domain.filter fun a => route₂ (route₁ a) = c).card
        <= (middleForC.biUnion fiber₁).card := hcard_cover
    _ <= middleForC.sum fun b => (fiber₁ b).card := hbi
    _ <= middleForC.sum fun _b => K₁ := hsum_bound
    _ = middleForC.card * K₁ := hsumK
    _ <= K₂ * K₁ := Nat.mul_le_mul_right K₁ hmiddle_card
    _ = K₁ * K₂ := by rw [Nat.mul_comm]

/--
Tail-threshold induction.

If a cofinal tail is contradictory at a base threshold `B0`, and the
contradiction is inherited when the threshold is advanced from `B` to `B+1`,
then every later threshold is contradictory.
-/
theorem cofinalTailContradicts_of_base_and_successor
    {Exception : Nat -> Prop} {B0 : Nat}
    (hbase : CofinalTailContradicts Exception B0)
    (hstep :
      forall B,
        B0 <= B ->
          CofinalTailContradicts Exception B ->
            CofinalTailContradicts Exception (B + 1)) :
    forall B, B0 <= B -> CofinalTailContradicts Exception B := by
  exact Nat.le_induction hbase hstep

/--
No cofinal tail exists if a base threshold is contradictory and that
contradiction is inherited by every successor threshold.

This is the formal version of the "prove the base prefix, then shift the tail
start by one and lengthen the prefix" argument.  The successor step is the
place where a concrete pressure-growth or certificate-inheritance theorem must
be supplied.
-/
theorem no_cofinalTail_of_base_and_successor_contradiction
    {Exception : Nat -> Prop} {B0 : Nat}
    (hbase : CofinalTailContradicts Exception B0)
    (hstep :
      forall B,
        B0 <= B ->
          CofinalTailContradicts Exception B ->
            CofinalTailContradicts Exception (B + 1)) :
    Not (exists B, CofinalExceptionTail Exception B) := by
  intro htail
  rcases htail with ⟨B, tailB⟩
  by_cases hB0B : B0 <= B
  · exact
      (cofinalTailContradicts_of_base_and_successor hbase hstep
        B hB0B) tailB
  · have hBB0 : B <= B0 := by omega
    exact hbase (cofinalTail_mono_threshold hBB0 tailB)

def BoundedTwinMids : Prop :=
  exists M,
    forall m, M < m ->
      Not (Nat.Prime (m - 1) /\ Nat.Prime (m + 1))

def ArbitrarilyLargeTwins : Prop :=
  forall N, exists p, N <= p /\ Nat.Prime p /\ Nat.Prime (p + 2)

/-- Row indices for the midpoint row attached to `r`. -/
def MidpointRowIndex (r h : Nat) : Prop :=
  1 <= h /\ h < r

/-- Midpoint of the twin pair attached to prime parameter `r` and index `h`. -/
def MidpointRowMidpoint (r h : Nat) : Nat :=
  r * h

/-- A twin pair around the midpoint `r * h`. -/
def MidpointTwinWitnessAt (r h : Nat) : Prop :=
  Nat.Prime (MidpointRowMidpoint r h - 1) /\
    Nat.Prime (MidpointRowMidpoint r h + 1)

/--
Midpoint-exceptional prime: `r` is prime and no row index gives a twin pair
around `r * h`.
-/
def MidpointExceptionalPrime (r : Nat) : Prop :=
  Nat.Prime r /\
    forall h, MidpointRowIndex r h -> Not (MidpointTwinWitnessAt r h)

/--
A composite natural below `r^2` has a prime divisor below `r`.

This is the elementary size estimate used by row descent: once a row neighbor
is composite and the row index is below `r`, some prime divisor must descend
below the parent prime.
-/
lemma exists_prime_dvd_lt_of_not_prime_lt_square
    {n r : Nat}
    (hn2 : 2 <= n)
    (hnnot : Not (Nat.Prime n))
    (hnlt : n < r * r) :
    exists q, Nat.Prime q /\ q < r /\ q ∣ n := by
  rcases Nat.exists_dvd_of_not_prime2 hn2 hnnot with ⟨m, hmdvd, hm2, hmn⟩
  rcases hmdvd with ⟨k, hk⟩
  have hsqrt : m <= Nat.sqrt n ∨ k <= Nat.sqrt n := by
    exact Nat.le_sqrt_of_eq_mul hk
  have hsqrtr : Nat.sqrt n < r := by
    exact Nat.sqrt_lt.mpr hnlt
  rcases hsqrt with hm_sqrt | hk_sqrt
  · have hmne : m ≠ 1 := by omega
    rcases Nat.exists_prime_and_dvd hmne with ⟨q, hqprime, hqdm⟩
    have hqle_m : q <= m := Nat.le_of_dvd (by omega) hqdm
    refine ⟨q, hqprime, lt_of_le_of_lt ?_ hsqrtr, ?_⟩
    · exact le_trans hqle_m hm_sqrt
    · exact dvd_trans hqdm ⟨k, hk⟩
  · have hkpos : 0 < k := by
      by_contra hnot
      have hk0 : k = 0 := by omega
      subst k
      simp at hk
      omega
    have hkne : k ≠ 1 := by
      intro hk1
      subst k
      simp at hk
      omega
    rcases Nat.exists_prime_and_dvd hkne with ⟨q, hqprime, hqdk⟩
    have hqle_k : q <= k := Nat.le_of_dvd hkpos hqdk
    refine ⟨q, hqprime, lt_of_le_of_lt ?_ hsqrtr, ?_⟩
    · exact le_trans hqle_k hk_sqrt
    · rw [hk]
      exact dvd_mul_of_dvd_right hqdk m

/--
Every exceptional midpoint row descends to a smaller prime divisor on at least
one side.

This is the finite-twins-to-descent brick: if `r` is exceptional, then neither
side can form a twin pair at any legal row index. Since both row neighbors are
positive and below `r^2`, one non-prime side supplies a prime divisor `< r`.
-/
theorem MidpointExceptionalPrime.exists_descending_prime_divisor
    {r h : Nat}
    (hex : MidpointExceptionalPrime r)
    (hr3 : 3 <= r)
    (hidx : MidpointRowIndex r h) :
    exists q, Nat.Prime q /\ q < r /\
      (q ∣ MidpointRowMidpoint r h - 1 \/
        q ∣ MidpointRowMidpoint r h + 1) := by
  let a := MidpointRowMidpoint r h - 1
  let b := MidpointRowMidpoint r h + 1
  have hnotBoth : Not (Nat.Prime a /\ Nat.Prime b) := by
    exact hex.2 h hidx
  have hrpos : 0 < r := by omega
  have hprod_ge_r : r <= r * h := by
    calc
      r = r * 1 := by rw [Nat.mul_one]
      _ <= r * h := Nat.mul_le_mul_left r hidx.1
  have hprod_ge3 : 3 <= r * h := le_trans hr3 hprod_ge_r
  have hprod_lt_square : r * h < r * r :=
    Nat.mul_lt_mul_of_pos_left hidx.2 hrpos
  have ha2_raw : 2 <= r * h - 1 := by omega
  have hb2_raw : 2 <= r * h + 1 := by omega
  have halt_raw : r * h - 1 < r * r :=
    lt_of_le_of_lt (Nat.sub_le _ _) hprod_lt_square
  have hblt_raw : r * h + 1 < r * r := by
    have h1r : 1 < r := by omega
    have hstep : r * h + 1 < r * h + r :=
      Nat.add_lt_add_left h1r (r * h)
    have hmul : r * h + r = r * (h + 1) := by ring
    have hhle : h + 1 <= r := Nat.succ_le_of_lt hidx.2
    have hle : r * (h + 1) <= r * r := Nat.mul_le_mul_left r hhle
    rw [hmul] at hstep
    exact lt_of_lt_of_le hstep hle
  have ha2 : 2 <= a := by
    simpa [a, MidpointRowMidpoint] using ha2_raw
  have hb2 : 2 <= b := by
    simpa [b, MidpointRowMidpoint] using hb2_raw
  have halt : a < r * r := by
    simpa [a, MidpointRowMidpoint] using halt_raw
  have hblt : b < r * r := by
    simpa [b, MidpointRowMidpoint] using hblt_raw
  by_cases hpa : Nat.Prime a
  · have hpnb : Not (Nat.Prime b) := by
      intro hpb
      exact hnotBoth ⟨hpa, hpb⟩
    rcases exists_prime_dvd_lt_of_not_prime_lt_square hb2 hpnb hblt with
      ⟨q, hqprime, hqr, hqdb⟩
    refine ⟨q, hqprime, hqr, Or.inr ?_⟩
    simpa [b] using hqdb
  · rcases exists_prime_dvd_lt_of_not_prime_lt_square ha2 hpa halt with
      ⟨q, hqprime, hqr, hqda⟩
    refine ⟨q, hqprime, hqr, Or.inl ?_⟩
    simpa [a] using hqda

/--
One deterministic-free descent edge from a midpoint-exceptional prime row.

For the generic descent-to-tail-start theorem below we only use the row
`h = 1`, so the midpoint is `r` itself and the edge records a smaller prime
divisor of either `r - 1` or `r + 1`.
-/
def MidpointPrimeDescentEdge (r q : Nat) : Prop :=
  Nat.Prime r ∧ Nat.Prime q ∧ q < r ∧ (q ∣ r - 1 ∨ q ∣ r + 1)

/--
The generic `h = 1` descent is too weak to prove MP/PM pressure by itself:
every odd prime can take the trivial small-prime edge through `2`.

This theorem is a useful guardrail for the endpoint.  It explains why
"descent reaches below `B`" does not imply "fresh MP/PM event"; without a
prewheeled or event-producing route law, all generic descents may collide at a
small sink.
-/
theorem odd_prime_has_two_descent_edge
    {r : Nat}
    (hr : Nat.Prime r)
    (hr2 : 2 < r) :
    MidpointPrimeDescentEdge r 2 := by
  have hodd : r % 2 = 1 := by
    cases hr.eq_two_or_odd with
    | inl htwo =>
        subst r
        omega
    | inr hodd =>
        exact hodd
  have hdiv : Dvd.dvd 2 (r - 1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  constructor
  · exact hr
  constructor
  · norm_num
  constructor
  · exact hr2
  · exact Or.inl hdiv

/--
A finite strict descent path from `r` to a terminal prime `terminal` at or
below the moving bound `B`.
-/
inductive MidpointPrimeDescentPathBelow (B : Nat) : Nat -> Nat -> Prop
  | done {r : Nat} :
      Nat.Prime r ->
        r <= B ->
          MidpointPrimeDescentPathBelow B r r
  | step {r q terminal : Nat} :
      MidpointPrimeDescentEdge r q ->
        MidpointPrimeDescentPathBelow B q terminal ->
          MidpointPrimeDescentPathBelow B r terminal

/--
Under a cofinal exceptional tail, generic smaller-prime descent cannot get
stuck above the tail start.

This is deliberately not an MP/PM event theorem.  It proves the structural
descent fact: start with any prime `r > B` in a cofinal exceptional tail, and
repeatedly use the row `h = 1`; since each step moves to a smaller prime, some
finite path reaches a prime at or below `B`.
-/
theorem cofinalTail_exists_primeDescentPathBelow
    {B r : Nat}
    (hB2 : 2 <= B)
    (tail : CofinalExceptionTail MidpointExceptionalPrime B)
    (hr : Nat.Prime r)
    (hBr : B < r) :
    exists terminal,
      terminal <= B ∧ Nat.Prime terminal ∧
        MidpointPrimeDescentPathBelow B r terminal := by
  classical
  induction r using Nat.strong_induction_on generalizing B with
  | h r ih =>
    by_cases hrBelow : r <= B
    · exact ⟨r, hrBelow, hr, MidpointPrimeDescentPathBelow.done hr hrBelow⟩
    · have hBr' : B < r := lt_of_not_ge hrBelow
      have hr3 : 3 <= r := by
        have h2r : 2 < r := lt_of_le_of_lt hB2 hBr'
        omega
      have hidx : MidpointRowIndex r 1 := by
        constructor <;> omega
      have hex : MidpointExceptionalPrime r := tail r hr hBr'
      rcases hex.exists_descending_prime_divisor hr3 hidx with
        ⟨q, hqPrime, hqr, hqdiv⟩
      have hedge : MidpointPrimeDescentEdge r q := by
        constructor
        · exact hr
        constructor
        · exact hqPrime
        constructor
        · exact hqr
        · simpa [MidpointRowMidpoint] using hqdiv
      by_cases hqBelow : q <= B
      · exact ⟨q, hqBelow, hqPrime,
          MidpointPrimeDescentPathBelow.step hedge
            (MidpointPrimeDescentPathBelow.done hqPrime hqBelow)⟩
      · have hBq : B < q := lt_of_not_ge hqBelow
        rcases ih q hqr hB2 tail hqPrime hBq with
          ⟨terminal, hterminalB, hterminalPrime, hpath⟩
        exact ⟨terminal, hterminalB, hterminalPrime,
          MidpointPrimeDescentPathBelow.step hedge hpath⟩

/--
Bounded twin midpoints force a cofinal tail of midpoint-exceptional primes.

This is the only global arithmetic bridge in the minimal Lean core.
-/
theorem boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime
    (hbounded : BoundedTwinMids) :
    exists B, CofinalExceptionTail MidpointExceptionalPrime B := by
  rcases hbounded with ⟨M, hnoTwinsAbove⟩
  refine ⟨M, ?_⟩
  intro r hr hMr
  constructor
  · exact hr
  · intro h hidx htwin
    have hr_le_center : r <= MidpointRowMidpoint r h := by
      unfold MidpointRowMidpoint
      calc
        r = r * 1 := by rw [Nat.mul_one]
        _ <= r * h := Nat.mul_le_mul_left r hidx.1
    have hM_center : M < MidpointRowMidpoint r h :=
      lt_of_lt_of_le hMr hr_le_center
    exact hnoTwinsAbove (MidpointRowMidpoint r h) hM_center htwin

/-- A cofinal tail gives a first exception after any verified gap. -/
theorem cofinalTail_gives_firstExceptionAfterGap
    {Exception : Nat -> Prop} {B : Nat}
    (tail : CofinalExceptionTail Exception B)
    (gap : ObservedExceptionGap) :
    Nonempty (FirstExceptionAfterGap Exception gap) := by
  classical
  let pred : Nat -> Prop :=
    fun p => gap.verifiedTo < p /\ Nat.Prime p /\ Exception p
  have hexists : Exists pred := by
    rcases Nat.exists_infinite_primes (max B gap.verifiedTo + 1) with
      ⟨r, hrgt, hrPrime⟩
    have hmax : max B gap.verifiedTo < r := by
      omega
    have hB : B < r := lt_of_le_of_lt (le_max_left _ _) hmax
    have hG : gap.verifiedTo < r := lt_of_le_of_lt (le_max_right _ _) hmax
    exact ⟨r, hG, hrPrime, tail r hrPrime hB⟩
  let R := Nat.find hexists
  have hR : pred R := Nat.find_spec hexists
  refine ⟨{
    r := R
    hr := hR.2.1
    hafter := hR.1
    exception := hR.2.2
    first_after_gap := ?_
  }⟩
  intro s hsPrime hsAfter hsLt hsException
  have hsPred : pred s := ⟨hsAfter, hsPrime, hsException⟩
  have hmin : R <= s := Nat.find_min' hexists hsPred
  omega

/--
First-exception monotonicity: a first exception after a later verified bound
gives a first exception after any earlier verified bound.
-/
theorem firstException_mono_backward
    {Exception : Nat -> Prop}
    {gapSmall gapLarge : ObservedExceptionGap}
    (hle : gapSmall.verifiedTo <= gapLarge.verifiedTo)
    (firstException : FirstExceptionAfterGap Exception gapLarge) :
    Nonempty (FirstExceptionAfterGap Exception gapSmall) := by
  classical
  let pred : Nat -> Prop :=
    fun p => gapSmall.verifiedTo < p /\ Nat.Prime p /\ Exception p
  have hexists : Exists pred := by
    exact ⟨firstException.r,
      lt_of_le_of_lt hle firstException.hafter,
      firstException.hr,
      firstException.exception⟩
  let R := Nat.find hexists
  have hR : pred R := Nat.find_spec hexists
  refine ⟨{
    r := R
    hr := hR.2.1
    hafter := hR.1
    exception := hR.2.2
    first_after_gap := ?_
  }⟩
  intro s hsPrime hsAfter hsLt hsException
  have hsPred : pred s := ⟨hsAfter, hsPrime, hsException⟩
  have hmin : R <= s := Nat.find_min' hexists hsPred
  omega

theorem no_firstException_mono_forward
    {Exception : Nat -> Prop}
    {gapSmall gapLarge : ObservedExceptionGap}
    (hle : gapSmall.verifiedTo <= gapLarge.verifiedTo)
    (hno : Not (Nonempty (FirstExceptionAfterGap Exception gapSmall))) :
    Not (Nonempty (FirstExceptionAfterGap Exception gapLarge)) := by
  intro hlarge
  rcases hlarge with ⟨firstException⟩
  exact hno (firstException_mono_backward hle firstException)

theorem arbitrarily_large_twins_of_not_boundedTwinMids
    (hnotBounded : Not BoundedTwinMids) :
    ArbitrarilyLargeTwins := by
  intro N
  by_contra hnone
  apply hnotBounded
  refine ⟨N + 1, ?_⟩
  intro m hm hpair
  apply hnone
  refine ⟨m - 1, ?_, ?_, ?_⟩
  · omega
  · exact hpair.1
  · have hshift : m - 1 + 2 = m + 1 := by
      omega
    simpa [hshift] using hpair.2

theorem no_boundedTwinMids_of_no_cofinalExceptionTail
    (hno :
      Not (exists B,
        CofinalExceptionTail MidpointExceptionalPrime B)) :
    Not BoundedTwinMids := by
  intro hbounded
  exact hno
    (boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime hbounded)

theorem arbitrarily_large_twins_of_no_cofinalExceptionTail
    (hno :
      Not (exists B,
        CofinalExceptionTail MidpointExceptionalPrime B)) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_not_boundedTwinMids
    (no_boundedTwinMids_of_no_cofinalExceptionTail hno)

theorem no_boundedTwinMids_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not BoundedTwinMids := by
  intro hbounded
  rcases boundedTwinMids_forces_cofinalTail_midpointExceptionalPrime
      hbounded with ⟨B, tail⟩
  exact hno
    (cofinalTail_gives_firstExceptionAfterGap
      tail certificateExceptionGap)

/-- Lean endpoint from a certificate forbidding the first exception after the certificate gap. -/
theorem arbitrarily_large_twins_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_not_boundedTwinMids
    (no_boundedTwinMids_of_no_certificateFirstException hno)

/--
A no-first-exception certificate at the certificate threshold also rules out
any later verified gap, including the observed gap.
-/
theorem no_later_firstException_of_no_certificateFirstException
    {gapLarge : ObservedExceptionGap}
    (hle : certificateExceptionGap.verifiedTo <= gapLarge.verifiedTo)
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not (Nonempty
      (FirstExceptionAfterGap MidpointExceptionalPrime gapLarge)) :=
  no_firstException_mono_forward hle hno

theorem no_observed_firstException_of_no_certificateFirstException
    (hno :
      Not (Nonempty
        (FirstExceptionAfterGap MidpointExceptionalPrime
          certificateExceptionGap))) :
    Not (Nonempty
      (FirstExceptionAfterGap MidpointExceptionalPrime observedExceptionGap)) :=
  no_later_firstException_of_no_certificateFirstException
    certificateVerifiedTo_le_observed hno

end TwinPrimeCertificate


