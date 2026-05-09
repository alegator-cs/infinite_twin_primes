# Twin Prime Conditional Endpoint

This repository contains a minimal Lean endpoint for several closely related
moving-window and event-pressure proof shapes. The default build no longer
imports the generated routed MP/PM shard tree.

The strongest default-facing endpoint is conditional on a concrete
moving-window event-pressure certificate:

```lean
TwinPrimeCertificate.UniqueDescentEndpoint
  .arbitrarily_large_twins_of_movingWindowEventPressure
```

Its certificate requires two concrete facts:

```lean
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
```

The proof path is:

1. A finite-twins hypothesis gives a cofinal tail of midpoint-exceptional
   primes.
2. The event-pressure certificate supplies, after any bound, finitely many
   eligible seeds whose produced event union is larger than the finite slot
   window.
3. The cofinal tail makes all sufficiently large selected seeds
   midpoint-exceptional.
4. The landing theorem sends every produced event into `slots B`.
5. This gives a strict cardinality contradiction.
6. No cofinal exceptional tail exists, so twin primes are arbitrarily large.

The remaining mathematical content is exactly the event-pressure certificate:
fresh eligible starts must create enough distinct MP/PM events in the moving
finite window. Lean also exposes a unique-descent/finite-ancestor endpoint, but
that endpoint is stronger than currently justified by the generic descent
theorem because fresh starts alone do not rule out event collisions.

## DFI/Toth Root-Supply Bridge

The file `TwinPrimeCertificate/QuadraticRootSupply.lean` isolates the weakest
analytic input that currently looks capable of closing the successor-recovery
gap. It does not add an axiom. Instead it proves, in Lean, that the following
peer-reviewed-theorem-shaped corollary is enough:

```lean
structure QuadraticRootParentSupply
    (events : Finset Event)
    (ProducedEvents : Nat -> Finset Event) where
  root_after : ...
  root_produces : ...
```

Informally, `root_after` says that for every lost finite event and every lower
bound `N`, there is a later split prime `p ≡ 1 [MOD 5]` with a legal root of
one of the two quadratic row polynomials in the required residue class. This is
exactly the Duke--Friedlander--Iwaniec / Toth root-equidistribution input, not
plain Dirichlet in arithmetic progressions.

Lean then proves:

```lean
exists_exact_eligible_recovery_batch_after_shift_of_quadraticRootSupply
```

So the current honest closure point is:

1. DFI/Toth-style root supply gives arbitrarily late parents for each lost
   event.
2. Lean turns one-parent-after-any-bound into multiplicity two.
3. Lean turns multiplicity two into exact shifted-tail event recovery.
4. The existing tail-induction endpoint consumes the corresponding successor
   recovery certificate.

## Main Lean Files

```text
TwinPrimeCertificate/Core.lean
TwinPrimeCertificate/RecursiveMPPMCertificate.lean
TwinPrimeCertificate/DescentPressure.lean
TwinPrimeCertificate/QuadraticRootSupply.lean
TwinPrimeCertificate/FiniteSinkAvoidance.lean
TwinPrimeCertificate/TailInductionCertificate.lean
TwinPrimeCertificate/Final.lean
TwinPrimeCertificate/UniqueDescentEndpoint.lean
TwinPrimeCertificate.lean
```

The older generated routed-chain files remain in the repository as optional
audit material, but they are not imported by `TwinPrimeCertificate.lean`.

## Build

```bash
lake build
```

## Checks

Placeholder scan for the default endpoint files:

```bash
rg -n "\b(sorry|admit|axiom|constant)\b" \
  TwinPrimeCertificate.lean \
  TwinPrimeCertificate/Core.lean \
  TwinPrimeCertificate/RecursiveMPPMCertificate.lean \
  TwinPrimeCertificate/DescentPressure.lean \
  TwinPrimeCertificate/QuadraticRootSupply.lean \
  TwinPrimeCertificate/FiniteSinkAvoidance.lean \
  TwinPrimeCertificate/TailInductionCertificate.lean \
  TwinPrimeCertificate/Final.lean \
  TwinPrimeCertificate/UniqueDescentEndpoint.lean
```

Expected output: no matches.

Axiom check:

```bash
lake env lean --stdin <<'EOF'
import TwinPrimeCertificate.UniqueDescentEndpoint
#print axioms TwinPrimeCertificate.UniqueDescentEndpoint.arbitrarily_large_twins_of_movingWindowEventPressure
EOF
```

Expected project-specific axioms: none. Standard Lean axioms such as
`propext`, `Classical.choice`, and `Quot.sound` may appear.
