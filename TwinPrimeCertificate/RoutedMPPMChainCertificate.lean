import TwinPrimeCertificate.RecursiveMPPMCertificate

/-!
# Lean-Checkable Recursive MP/PM Route Chains

This file gives generated route-chain shards a small Boolean checker.

The generated data is deliberately arithmetic rather than semantic: each chain
records concrete quadratic rows, concrete decreasing descended-prime edges, and
a concrete terminal side-event encoding.  Lean checks those facts by evaluation.
The remaining mathematical bridge is the theorem that such checked chains are
indeed realized under a cofinal exceptional tail.
-/

namespace TwinPrimeCertificate.RoutedMPPMChainCertificate

def X : Nat := 30000000

/-- `typ = 0` is the left row, `typ = 1` is the right row. -/
def rowProduct (typ u : Nat) : Nat :=
  if typ = 0 then
    u * (u + 3) + 1
  else
    (u + 1) * (u + 4) + 1

def rowValid (p typ u h : Nat) : Bool :=
  (typ == 0 || typ == 1) &&
    (1 <= h) &&
    (h < p) &&
    (p * h == rowProduct typ u)

theorem rowValid_typ_left_or_right
    {p typ u h : Nat}
    (hvalid : rowValid p typ u h = true) :
    typ = 0 \/ typ = 1 := by
  unfold rowValid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  simpa using h₃.1

theorem rowValid_h_pos
    {p typ u h : Nat}
    (hvalid : rowValid p typ u h = true) :
    1 <= h := by
  unfold rowValid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact of_decide_eq_true h₃.2

theorem rowValid_h_lt_parent
    {p typ u h : Nat}
    (hvalid : rowValid p typ u h = true) :
    h < p := by
  unfold rowValid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact of_decide_eq_true h₂.2

theorem rowValid_mul_eq
    {p typ u h : Nat}
    (hvalid : rowValid p typ u h = true) :
    p * h = rowProduct typ u := by
  unfold rowValid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  exact of_decide_eq_true h₁.2

def slotValue (u slot : Nat) : Nat :=
  u + slot

structure EdgeWitness where
  parent : Nat
  child : Nat
  typ : Nat
  u : Nat
  h : Nat
  slot : Nat
  quotient : Nat
deriving Repr, DecidableEq

namespace EdgeWitness

def valid (edge : EdgeWitness) : Bool :=
  rowValid edge.parent edge.typ edge.u edge.h &&
    (edge.slot <= 4) &&
    (edge.child < edge.parent) &&
    (edge.child * edge.quotient == slotValue edge.u edge.slot)

theorem rowValid_of_valid
    {edge : EdgeWitness}
    (hvalid : edge.valid = true) :
    rowValid edge.parent edge.typ edge.u edge.h = true := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact h₃.1

theorem slot_le_four_of_valid
    {edge : EdgeWitness}
    (hvalid : edge.valid = true) :
    edge.slot <= 4 := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact of_decide_eq_true h₃.2

theorem child_lt_parent_of_valid
    {edge : EdgeWitness}
    (hvalid : edge.valid = true) :
    edge.child < edge.parent := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact of_decide_eq_true h₂.2

theorem quotient_mul_eq_slotValue_of_valid
    {edge : EdgeWitness}
    (hvalid : edge.valid = true) :
    edge.child * edge.quotient = slotValue edge.u edge.slot := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  exact of_decide_eq_true h₁.2

end EdgeWitness

structure DirectEventWitness where
  parent : Nat
  typ : Nat
  u : Nat
  h : Nat
  k : Nat
  targetU : Nat
  side : Nat
  eventId : Nat
  code : Nat
deriving Repr, DecidableEq

namespace DirectEventWitness

def valid (w : DirectEventWitness) : Bool :=
  rowValid w.parent w.typ w.u w.h &&
    (w.targetU == w.u + w.k * w.parent) &&
    (w.targetU < X) &&
    (w.side < 2) &&
    (w.code == TwinPrimeCertificate.encodeSideEvent w.targetU w.side)

theorem rowValid_of_valid
    {w : DirectEventWitness}
    (hvalid : w.valid = true) :
    rowValid w.parent w.typ w.u w.h = true := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  have h₄ := (Bool.and_eq_true _ _).mp h₃.1
  exact h₄.1

theorem targetU_eq_of_valid
    {w : DirectEventWitness}
    (hvalid : w.valid = true) :
    w.targetU = w.u + w.k * w.parent := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  have h₄ := (Bool.and_eq_true _ _).mp h₃.1
  exact of_decide_eq_true h₄.2

theorem targetU_lt_X_of_valid
    {w : DirectEventWitness}
    (hvalid : w.valid = true) :
    w.targetU < X := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact of_decide_eq_true h₃.2

theorem side_lt_two_of_valid
    {w : DirectEventWitness}
    (hvalid : w.valid = true) :
    w.side < 2 := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact of_decide_eq_true h₂.2

theorem code_eq_of_valid
    {w : DirectEventWitness}
    (hvalid : w.valid = true) :
    w.code = TwinPrimeCertificate.encodeSideEvent w.targetU w.side := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  exact of_decide_eq_true h₁.2

end DirectEventWitness

structure ChainWitness where
  eventId : Nat
  code : Nat
  actual : Nat
  start : Nat
  edges : List EdgeWitness
  terminal : DirectEventWitness
deriving Repr, DecidableEq

namespace ChainWitness

def lastParentAux : Nat -> List EdgeWitness -> Nat
  | p, [] => p
  | _p, edge :: rest => lastParentAux edge.child rest

def lastParent (chain : ChainWitness) : Nat :=
  lastParentAux chain.start chain.edges

def chainConnectedAux : Nat -> List EdgeWitness -> Bool
  | _p, [] => true
  | p, edge :: rest =>
      (edge.parent == p) &&
        edge.valid &&
        chainConnectedAux edge.child rest

def valid (chain : ChainWitness) : Bool :=
  (chain.actual == 0 || chain.actual == 1) &&
    (chain.terminal.eventId == chain.eventId) &&
    (chain.terminal.code == chain.code) &&
    (chain.terminal.parent == chain.lastParent) &&
    chainConnectedAux chain.start chain.edges &&
    chain.terminal.valid

theorem terminal_valid_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.terminal.valid = true := by
  unfold valid at hvalid
  exact (Bool.and_eq_true _ _).mp hvalid |>.2

theorem terminal_targetU_lt_X_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.terminal.targetU < X :=
  DirectEventWitness.targetU_lt_X_of_valid
    (terminal_valid_of_valid hvalid)

theorem connectedAux_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chainConnectedAux chain.start chain.edges = true := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact h₂.2

theorem terminal_parent_eq_lastParent_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.terminal.parent = chain.lastParent := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  exact of_decide_eq_true h₃.2

theorem terminal_code_eq_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.terminal.code = chain.code := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  have h₄ := (Bool.and_eq_true _ _).mp h₃.1
  exact of_decide_eq_true h₄.2

theorem terminal_eventId_eq_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.terminal.eventId = chain.eventId := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  have h₄ := (Bool.and_eq_true _ _).mp h₃.1
  have h₅ := (Bool.and_eq_true _ _).mp h₄.1
  exact of_decide_eq_true h₅.2

theorem actual_zero_or_one_of_valid
    {chain : ChainWitness}
    (hvalid : chain.valid = true) :
    chain.actual = 0 \/ chain.actual = 1 := by
  unfold valid at hvalid
  have h₁ := (Bool.and_eq_true _ _).mp hvalid
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  have h₃ := (Bool.and_eq_true _ _).mp h₂.1
  have h₄ := (Bool.and_eq_true _ _).mp h₃.1
  have h₅ := (Bool.and_eq_true _ _).mp h₄.1
  simpa using h₅.1

theorem edge_valid_of_connectedAux_head
    {p : Nat} {edge : EdgeWitness} {rest : List EdgeWitness}
    (hconn : chainConnectedAux p (edge :: rest) = true) :
    edge.valid = true := by
  unfold chainConnectedAux at hconn
  have h₁ := (Bool.and_eq_true _ _).mp hconn
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact h₂.2

theorem edge_parent_eq_of_connectedAux_head
    {p : Nat} {edge : EdgeWitness} {rest : List EdgeWitness}
    (hconn : chainConnectedAux p (edge :: rest) = true) :
    edge.parent = p := by
  unfold chainConnectedAux at hconn
  have h₁ := (Bool.and_eq_true _ _).mp hconn
  have h₂ := (Bool.and_eq_true _ _).mp h₁.1
  exact of_decide_eq_true h₂.1

end ChainWitness

def StrictlyIncreasingById (chains : List ChainWitness) : Prop :=
  chains.Pairwise (fun a b => a.eventId < b.eventId)

def strictlyIncreasingIdsFrom : Nat -> List ChainWitness -> Bool
  | _previous, [] => true
  | previous, chain :: rest =>
      (previous < chain.eventId) &&
        strictlyIncreasingIdsFrom chain.eventId rest

def strictlyIncreasingIds : List ChainWitness -> Bool
  | [] => true
  | chain :: rest => strictlyIncreasingIdsFrom chain.eventId rest

def allValid (chains : List ChainWitness) : Bool :=
  chains.all ChainWitness.valid

def allStartsIn (lo hi : Nat) (chains : List ChainWitness) : Bool :=
  chains.all (fun chain => (lo <= chain.start) && (chain.start <= hi))

theorem chain_valid_of_allValid
    {chains : List ChainWitness}
    {chain : ChainWitness}
    (hall : allValid chains = true)
    (hmem : chain ∈ chains) :
    chain.valid = true :=
  (List.all_eq_true.mp hall) chain hmem

theorem chain_terminal_targetU_lt_X_of_allValid
    {chains : List ChainWitness}
    {chain : ChainWitness}
    (hall : allValid chains = true)
    (hmem : chain ∈ chains) :
    chain.terminal.targetU < X :=
  ChainWitness.terminal_targetU_lt_X_of_valid
    (chain_valid_of_allValid hall hmem)

def actualCount (chains : List ChainWitness) : Nat :=
  (chains.filter (fun c => c.actual == 1)).length

def falseCount (chains : List ChainWitness) : Nat :=
  (chains.filter (fun c => c.actual == 0)).length

end TwinPrimeCertificate.RoutedMPPMChainCertificate

