# Twin Prime External Certificate Endpoint

This repository contains the Lean endpoint and external certificate tooling for the finite-contradiction proof shape described in `paper/twin_prime_external_certificate_endpoint.pdf`.

Lean proves the endpoint from one external C++ route-realization bridge:

```lean
GeneratedCertificate.external_predictedEvents_realized_of_cofinalTail :
  (exists B, CofinalExceptionTail MidpointExceptionalPrime B) ->
    GeneratedCertificate.predictedEvents subseteq GeneratedCertificate.actualEvents
```

Everything after that declaration is Lean-checked:

1. bounded twin-prime midpoints imply a cofinal tail of midpoint-exceptional primes;
2. the recursive MP/PM certificate turns route realization into a finite set contradiction;
3. the generated C++ bridge supplies route realization for the predicted event set;
4. twin midpoints are unbounded;
5. twin primes are arbitrarily large.

The final theorem is:

```lean
TwinPrimeExternal.arbitrarily_large_twins :
  forall N, exists p, N <= p /\ Nat.Prime p /\ Nat.Prime (p + 2)
```

## Trust boundary

The file `TwinPrimeExternal/GeneratedCertificate.lean` intentionally contains
one final-theorem-relevant `axiom`. That declaration is the external C++
route-realization dependency. The rest of the endpoint is ordinary Lean proof.

The auxiliary file `TwinPrimeExternal/GeneratedGapCertificate.lean` contains a
second external declaration for the finite no-exception window after 127. It
documents the empirical starting point but is not a dependency of
`TwinPrimeExternal.arbitrarily_large_twins`.

The generated arithmetic currently records:

```text
firstOverflowRoot           = 191281
firstOverflowSpan           = 17
firstOverflowSplitRoots     = 1
firstOverflowRoutedStarts   = 1
generatedActualEventCount   = 95568
generatedPredictedEventCount= 181052
falsePredictedEventCount    = 115633
```

## Regenerate the certificate

There are four C++ tools:

* `tools/search_recursive_prefix_threshold.cpp` is the actual finite search.
  It consumes `certificates/generated_mppm_pressure_certificate.json` and emits
  the small count summary.
* `tools/generate_external_certificate.cpp` turns that summary into the Lean
  external certificate file.
* `tools/check_cone_survivor_gap.cpp` is the midpoint-row gap checker for the
  finite window used here.
* `tools/print_routing_example.cpp` prints the descent route displayed in the
  paper.

Run from the repository root with a C++17 compiler:

```bash
g++ -std=c++17 -O2 -Wall -Wextra -pedantic tools/check_cone_survivor_gap.cpp -o tools/check_cone_survivor_gap
./tools/check_cone_survivor_gap --last 127 --checked-to 191264 --json-out certificates/generated_gap_certificate_summary.json --lean-out TwinPrimeExternal/GeneratedGapCertificate.lean

g++ -std=c++17 -O2 -Wall -Wextra -pedantic tools/search_recursive_prefix_threshold.cpp -o tools/search_recursive_prefix_threshold
./tools/search_recursive_prefix_threshold --cert certificates/generated_mppm_pressure_certificate.json --rstart 191265 --max-span 20 --json-out certificates/generated_external_certificate_summary.json --print-every 1

g++ -std=c++17 -O2 -Wall -Wextra -pedantic tools/generate_external_certificate.cpp -o tools/generate_external_certificate
./tools/generate_external_certificate --input-json certificates/generated_external_certificate_summary.json --audit --lean-out TwinPrimeExternal/GeneratedCertificate.lean --json-out certificate.json
```

## Build

Run from the repository root:

```bash
lake build
```

## Expected axiom scan

The scan should find exactly the generated external certificate declarations:

```bash
rg -n "\b(sorry|admit|axiom|constant)\b" TwinPrimeExternal -g "*.lean"
```

Expected declarations:

* `GeneratedCertificate.external_predictedEvents_realized_of_cofinalTail`;
* `GeneratedGapCertificate.external_exceptionFree_to_certificateThreshold`.

