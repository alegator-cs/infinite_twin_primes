# Twin Prime Certificate Endpoint

This repository contains a Lean 4 endpoint for an inductive finite-base MP/PM
certificate route to arbitrarily large twin primes:

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

The successor-recovery step is supplied by a DFI/Toth-style corollary on roots
of quadratic congruences to prime moduli. That analytic corollary is not
formalized inside this Lean repository; it is cited as established mathematics
and represented by the narrow interface in
`TwinPrimeCertificate/QuadraticRootSupply.lean`. In this formulation, shifting a
tail start from `B` to `B + 1` may lose finitely many previously counted MP/PM
events. Successor recovery says those lost events can be recovered after a
finite lengthening of the later exceptional prefix. Lean proves that it is
enough to give each lost event arbitrarily late eligible split-prime parents.
Requesting two such parents past a bound gives multiplicity at least two; the
multiplicity-two lemma then produces an exact recovery batch, and tail induction
propagates the finite base contradiction to all later tail starts.

## Build Imports

`lake build` builds the full Lean library, including the generated routed MP/PM
shard tree. The aggregate module

```lean
import TwinPrimeCertificate
```

imports the generated certificate endpoint.

## Main Lean Files

```text
TwinPrimeCertificate/Core.lean
TwinPrimeCertificate/RecursiveMPPMCertificate.lean
TwinPrimeCertificate/DescentPressure.lean
TwinPrimeCertificate/QuadraticRootSupply.lean
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

is retained as research support for the successor-recovery program. Its runs
showed that event multiplicity is already high at the finite certificate scale
and tends to increase quickly in the tested ranges, which is why the
multiplicity-two successor step is a plausible and deliberately weak target.

The midpoint-exception audit tool

```text
tools/check_midpoint_exceptions.cpp
```

directly checks the row definition: for each prime `r <= N`, it searches
`1 <= h < r` for a twin pair `r*h - 1`, `r*h + 1`. By default it checks the
known exception list

```text
2, 5, 11, 13, 31, 37, 53, 61, 73, 79, 97, 127
```

and is intended to audit the larger empirical claim that there are no further
midpoint-exceptional primes through `10^9`.

From PowerShell with WSL:

```powershell
wsl.exe bash -lc 'cd /mnt/c/Users/Oleg/source/codex/lean/prime_sunit_wheel/twin_prime_external_certificate_endpoint && g++ -std=c++17 -O3 -Wall -Wextra -pedantic tools/check_midpoint_exceptions.cpp -o tools/check_midpoint_exceptions && ./tools/check_midpoint_exceptions --limit 1000000000 --progress 1000000'
```

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
