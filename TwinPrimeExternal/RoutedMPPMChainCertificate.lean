import TwinPrimeExternal.RecursiveMPPMCertificate

/-!
# Lean-Checkable Recursive MP/PM Route Chains

This file gives generated route-chain shards a small Boolean checker.

The generated data is deliberately arithmetic rather than semantic: each chain
records concrete quadratic rows, concrete decreasing descended-prime edges, and
a concrete terminal side-event encoding.  Lean checks those facts by evaluation.
The remaining mathematical bridge is the theorem that such checked chains are
indeed realized under a cofinal exceptional tail.
-/

namespace TwinPrimeExternal.RoutedMPPMChainCertificate

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
    (w.code == TwinPrimeExternal.encodeSideEvent w.targetU w.side)

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

def actualCount (chains : List ChainWitness) : Nat :=
  (chains.filter (fun c => c.actual == 1)).length

def falseCount (chains : List ChainWitness) : Nat :=
  (chains.filter (fun c => c.actual == 0)).length

end TwinPrimeExternal.RoutedMPPMChainCertificate
