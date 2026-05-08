# Twin Prime External Certificate Endpoint

This repository contains a minimal Lean endpoint and generated routed MP/PM
certificate shards for the finite-contradiction proof shape described in
`paper/twin_prime_external_certificate_endpoint.tex`.

The canonical endpoint is:

```lean
TwinPrimeExternal.GeneratedTailInductionCertificate
  .arbitrarily_large_twins_of_routedChainRealization
```

It has the type:

```lean
TwinPrimeExternal.RoutedChainRealizationCertificate ->
  TwinPrimeExternal.ArbitrarilyLargeTwins
```

The proof path is:

1. Lean checks 95,569 generated routed MP/PM descent chains.
2. Lean checks the finite cardinal inequality `95568 < 95569`.
3. A `RoutedChainRealizationCertificate` says that, under a cofinal
   exceptional tail, the checked routed chains are realized as finite target
   MP/PM events.
4. The route-chain overflow gives `Not exists B, CofinalExceptionTail ... B`.
5. The tail-induction interface packages the no-tail theorem.
6. The core endpoint proves arbitrarily large twin primes.

There are no `axiom`, `constant`, `sorry`, or `admit` declarations in the Lean
files. The remaining mathematical input is explicit as the argument
`RoutedChainRealizationCertificate`.

## Main Lean Files

```text
TwinPrimeExternal/Core.lean
TwinPrimeExternal/RecursiveMPPMCertificate.lean
TwinPrimeExternal/RoutedMPPMChainCertificate.lean
TwinPrimeExternal/GeneratedRoutedMPPMChains/*.lean
TwinPrimeExternal/RoutedMPPMChainBridge.lean
TwinPrimeExternal/TailInductionCertificate.lean
TwinPrimeExternal/Final.lean
TwinPrimeExternal/GeneratedTailInductionCertificate.lean
```

## Regenerate Routed Chain Shards

Compile the generator from the repository root:

```bash
g++ -std=c++17 -O2 -Wall -Wextra -pedantic \
  tools/generate_routed_mppm_chain_certificate.cpp \
  -o tools/generate_routed_mppm_chain_certificate
```

Run it:

```bash
./tools/generate_routed_mppm_chain_certificate \
  --cert certificates/generated_mppm_pressure_certificate.json \
  --out-dir TwinPrimeExternal/GeneratedRoutedMPPMChains \
  --start 191281 \
  --shard-size 1000
```

The generated shards are committed, so regeneration is only needed when changing
the certificate input or generator.

## Build

```bash
lake build TwinPrimeExternal
```

## Checks

Placeholder scan:

```bash
rg -n "\b(sorry|admit|axiom|constant)\b" TwinPrimeExternal -g "*.lean"
```

Expected output: no matches.

Axiom check:

```bash
lake env lean --stdin <<'EOF'
import TwinPrimeExternal.GeneratedTailInductionCertificate
#print axioms TwinPrimeExternal.GeneratedTailInductionCertificate.arbitrarily_large_twins_of_routedChainRealization
EOF
```

Expected project-specific axioms: none. Standard Lean axioms such as
`propext`, `Classical.choice`, and `Quot.sound` may appear.

