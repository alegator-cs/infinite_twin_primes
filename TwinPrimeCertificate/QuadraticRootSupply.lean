import TwinPrimeCertificate.DescentPressure
import TwinPrimeCertificate.RecursiveMPPMCertificate

/-!
# Quadratic Root Supply

This file isolates the analytic input suggested by the
Duke--Friedlander--Iwaniec / Toth theorem on roots of quadratic congruences.

The already-proved tail-shift recovery theorem in `DescentPressure` needs only
one arithmetic fact: every lost finite event has arbitrarily late eligible
split-prime ancestors. Since one arbitrarily late ancestor can be requested
twice, above the first one, this gives the multiplicity-two hypothesis needed
by the finite recovery theorem.

The final structure, `QuadraticRootParentSupply`, is the concrete row-shaped
version of that input. A future analytic formalization would prove its
`root_after` field from a DFI/Toth-style root equidistribution theorem.
-/

namespace TwinPrimeCertificate

/-- The two quadratic rows used by the recursive MP/PM descent. -/
inductive QuadraticRowSide where
  | left
  | right
deriving DecidableEq

/-- The integer value of a quadratic row at coordinate `u`. -/
def quadraticRowValue : QuadraticRowSide → Nat → Nat
  | QuadraticRowSide.left, u => u * (u + 3) + 1
  | QuadraticRowSide.right, u => (u + 1) * (u + 4) + 1

theorem quadraticRowValue_left (u : Nat) :
    quadraticRowValue QuadraticRowSide.left u = u * (u + 3) + 1 := rfl

theorem quadraticRowValue_right (u : Nat) :
    quadraticRowValue QuadraticRowSide.right u = (u + 1) * (u + 4) + 1 := rfl

/--
Event-level parent supply.

For every finite event under consideration and every lower bound `N`, there is
an eligible split prime `p > N` that produces that event.
-/
structure EventParentSupply
    {Event : Type} [DecidableEq Event]
    (events : Finset Event)
    (ProducedEvents : Nat → Finset Event) where
  parent_after :
    ∀ N event, event ∈ events →
      ∃ p, N < p ∧ ModFiveOnePrime p ∧ event ∈ ProducedEvents p

/--
An arbitrarily-late single-parent supply gives the multiplicity-two batches
required by `DescentPressure`.
-/
theorem multiplicity_two_after_of_eventParentSupply
    {Event : Type} [DecidableEq Event]
    {events : Finset Event}
    {ProducedEvents : Nat → Finset Event}
    (supply : EventParentSupply events ProducedEvents) :
    ∀ N event, event ∈ events →
      ∃ seeds : Finset Nat,
        (∀ p, p ∈ seeds → N < p) ∧
          (∀ p, p ∈ seeds → ModFiveOnePrime p) ∧
            2 ≤
              (seeds.filter fun p => event ∈ ProducedEvents p).card := by
  classical
  intro N event hevent
  rcases supply.parent_after N event hevent with
    ⟨p, hpAfter, hpEligible, hpEvent⟩
  rcases supply.parent_after p event hevent with
    ⟨q, hqAfterP, hqEligible, hqEvent⟩
  have hqAfter : N < q := lt_trans hpAfter hqAfterP
  have hp_ne_q : p ≠ q := by
    intro hpq
    subst q
    exact (Nat.lt_irrefl p) hqAfterP
  let seeds : Finset Nat := {p, q}
  refine ⟨seeds, ?_, ?_, ?_⟩
  · intro r hr
    simp [seeds] at hr
    rcases hr with rfl | rfl
    · exact hpAfter
    · exact hqAfter
  · intro r hr
    simp [seeds] at hr
    rcases hr with rfl | rfl
    · exact hpEligible
    · exact hqEligible
  · have hfilter :
        seeds.filter (fun r => event ∈ ProducedEvents r) = seeds := by
      apply Finset.filter_true_of_mem
      intro r hr
      simp [seeds] at hr
      rcases hr with rfl | rfl
      · exact hpEvent
      · exact hqEvent
    have hcard : seeds.card = 2 := by
      simp [seeds, hp_ne_q]
    rw [hfilter, hcard]

/--
Exact tail-shift recovery from arbitrarily-late event parents.

This is the practical bridge from a DFI/Toth-style parent supply into the
already-proved finite recovery theorem.
-/
theorem exists_exact_eligible_recovery_batch_after_shift_of_eventParentSupply
    {Event : Type} [DecidableEq Event]
    (oldEvents shiftedEvents : Finset Event)
    (ProducedEvents : Nat → Finset Event)
    (N : Nat)
    (supply : EventParentSupply (oldEvents \ shiftedEvents) ProducedEvents) :
    ∃ seeds : Finset Nat,
      (∀ p, p ∈ seeds → N < p) ∧
        (∀ p, p ∈ seeds → ModFiveOnePrime p) ∧
          oldEvents ⊆ shiftedEvents ∪ seeds.biUnion ProducedEvents := by
  exact exists_exact_eligible_recovery_batch_after_shift
    oldEvents shiftedEvents ProducedEvents N
    (multiplicity_two_after_of_eventParentSupply supply)

/--
Concrete quadratic-root parent supply.

For each event, choose a side, modulus, and target root residue. The
`root_after` field asks for arbitrarily late split primes `p` admitting a legal
row root `u` in that residue class, with row height `h < p`. The
`root_produces` field is the finite descent bookkeeping saying that such a
legal row parent indeed produces the event.

This is the narrow DFI/Toth-shaped theorem surface: root equidistribution should
prove `root_after`; the generated descent checker proves `root_produces`.
-/
structure QuadraticRootParentSupply
    {Event : Type} [DecidableEq Event]
    (events : Finset Event)
    (ProducedEvents : Nat → Finset Event) where
  side : Event → QuadraticRowSide
  modulus : Event → Nat
  residue : Event → Nat
  root_after :
    ∀ N event, event ∈ events →
      ∃ p u h,
        N < p ∧
          ModFiveOnePrime p ∧
            1 ≤ h ∧
              h < p ∧
                quadraticRowValue (side event) u = p * h ∧
                  Nat.ModEq (modulus event) u (residue event)
  root_produces :
    ∀ event p u h,
      event ∈ events →
        ModFiveOnePrime p →
          1 ≤ h →
            h < p →
              quadraticRowValue (side event) u = p * h →
                Nat.ModEq (modulus event) u (residue event) →
                  event ∈ ProducedEvents p

/-- Forget the row data and keep only the event-level parent supply. -/
def QuadraticRootParentSupply.toEventParentSupply
    {Event : Type} [DecidableEq Event]
    {events : Finset Event}
    {ProducedEvents : Nat → Finset Event}
    (supply : QuadraticRootParentSupply events ProducedEvents) :
    EventParentSupply events ProducedEvents where
  parent_after := by
    intro N event hevent
    rcases supply.root_after N event hevent with
      ⟨p, u, h, hpAfter, hpEligible, hhPos, hhLt, hrow, hres⟩
    exact ⟨p, hpAfter, hpEligible,
      supply.root_produces event p u h hevent hpEligible hhPos hhLt hrow hres⟩

/-- Quadratic-root supply implies exact shifted-tail recovery. -/
theorem exists_exact_eligible_recovery_batch_after_shift_of_quadraticRootSupply
    {Event : Type} [DecidableEq Event]
    (oldEvents shiftedEvents : Finset Event)
    (ProducedEvents : Nat → Finset Event)
    (N : Nat)
    (supply :
      QuadraticRootParentSupply (oldEvents \ shiftedEvents) ProducedEvents) :
    ∃ seeds : Finset Nat,
      (∀ p, p ∈ seeds → N < p) ∧
        (∀ p, p ∈ seeds → ModFiveOnePrime p) ∧
          oldEvents ⊆ shiftedEvents ∪ seeds.biUnion ProducedEvents := by
  exact exists_exact_eligible_recovery_batch_after_shift_of_eventParentSupply
    oldEvents shiftedEvents ProducedEvents N supply.toEventParentSupply

end TwinPrimeCertificate
