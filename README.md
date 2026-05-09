# Twin Prime Certificate Endpoint

This repository contains a Lean 4 endpoint for the finite-base MP/PM
certificate route to arbitrarily large twin primes.

The preferred public endpoint is the generated finite-base certificate plus a
DFI/Toth-style successor-recovery input:

```lean
TwinPrimeCertificate.GeneratedTailInductionCertificate
  .arbitrarily_large_twins_of_generatedSuccessorRecovery
```

The theorem takes one explicit certificate:

```lean
structure GeneratedSuccessorRecoveryCertificate where
  base : RoutedBaseCaseRealizationCertificate
  successor_recovery :
    forall B,
      certificateVerifiedTo <= B ->
        CofinalTailContradicts MidpointExceptionalPrime B ->
          CofinalTailContradicts MidpointExceptionalPrime (B + 1)
```

This is the route we currently mean by "the certificate approach".

## Proof Shape

The proof path is:

1. If twin-prime midpoints were bounded, then midpoint-exceptional primes would
   form a cofinal tail.
2. The generated routed MP/PM shard certificate proves the finite base overflow
   at `certificateVerifiedTo`.
3. The successor-recovery input says that once a cofinal tail beginning at `B`
   is contradictory, the shifted tail beginning at `B + 1` is contradictory
   too.
4. Tail induction rules out every possible cofinal exceptional tail.
5. No cofinal exceptional tail implies unbounded twin-prime midpoints.
6. Unbounded twin-prime midpoints imply arbitrarily large twin primes.

The concrete base certificate is checked inside Lean by the generated shard
tree:

```lean
TwinPrimeCertificate.GeneratedRoutedMPPMChains.Index
```

The shard tree verifies 95,569 routed MP/PM chain witnesses against the finite
cap

```lean
generatedMPPMCard = 95568
```

The remaining mathematical input is the successor-recovery theorem. The file
`TwinPrimeCertificate/QuadraticRootSupply.lean` isolates the intended
DFI/Toth-shaped route to that input: quadratic roots in the two MP/PM row
families should provide arbitrarily late eligible parents for each lost event,
which Lean then turns into exact shifted-tail recovery.

The repository also contains a separate moving-window event-pressure surface in
`TwinPrimeCertificate/UniqueDescentEndpoint.lean`, but that is not the preferred
generated-certificate endpoint described here.

## Important Import Distinction

`lake build` builds the full Lean library, including the generated routed MP/PM
shard tree.

The lightweight aggregate module

```lean
import TwinPrimeCertificate
```

does not import the generated shard tree. To inspect the preferred certificate
endpoint, import:

```lean
import TwinPrimeCertificate.GeneratedTailInductionCertificate
```

## Main Lean Files

```text
TwinPrimeCertificate/Core.lean
TwinPrimeCertificate/RecursiveMPPMCertificate.lean
TwinPrimeCertificate/DescentPressure.lean
TwinPrimeCertificate/QuadraticRootSupply.lean
TwinPrimeCertificate/FiniteSinkAvoidance.lean
TwinPrimeCertificate/TailInductionCertificate.lean
TwinPrimeCertificate/Final.lean
TwinPrimeCertificate/GeneratedTailInductionCertificate.lean
TwinPrimeCertificate/RoutedMPPMChainCertificate.lean
TwinPrimeCertificate/RoutedMPPMChainBridge.lean
TwinPrimeCertificate/GeneratedRoutedMPPMChains/Index.lean
TwinPrimeCertificate/GeneratedRoutedMPPMChains/ShardNNN.lean
TwinPrimeCertificate.lean
```

## Tools and Certificates

The C++ generator

```text
tools/generate_routed_mppm_chain_certificate.cpp
```

emits the Lean shard files in

```text
TwinPrimeCertificate/GeneratedRoutedMPPMChains/
```

The C++ program is tooling. The certificate actually consumed by the proof is
the generated Lean code, which Lake checks.

The exploratory audit tool

```text
tools/audit_k2_forward.cpp
```

is retained as research support for the successor-recovery program.

## Build

```bash
lake build
```

Expected result:

```text
Build completed successfully
```

## Placeholder Scan

```bash
rg -n "\b(sorry|admit|axiom|constant)\b" TwinPrimeCertificate -g "*.lean"
```

Expected output: no matches.

## Axiom Check

```bash
lake env lean --stdin <<'EOF'
import TwinPrimeCertificate.GeneratedTailInductionCertificate
#print axioms TwinPrimeCertificate.GeneratedTailInductionCertificate.arbitrarily_large_twins_of_generatedSuccessorRecovery
EOF
```

Expected project-specific axioms: none. Standard Lean axioms such as
`propext`, `Classical.choice`, and `Quot.sound` may appear.

## Paper

The paper source and rendered PDF are:

```text
paper/twin_prime_certificate_endpoint.tex
paper/twin_prime_certificate_endpoint.pdf
```

The paper includes a Lean object index so a reader can match the prose proof to
the formal declarations.
