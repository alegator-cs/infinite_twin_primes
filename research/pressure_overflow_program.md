# Pressure Overflow Research Program

This memo records the current proof boundary and the research program for
turning infinite midpoint exceptions into an overflow of finite MP/PM slots.

## Current Lean Boundary

The default Lean endpoint is conditional on:

```lean
MovingWindowEventPressureCertificate
```

The certificate states that for every moving finite window `slots B` and every
lower search bound `N`, there is a finite batch of eligible split-prime seeds
whose produced MP/PM event union is larger than `slots B`, and whose produced
events all land in `slots B` once the seeds are midpoint-exceptional.

Lean already proves:

* finite twin midpoints imply a cofinal tail of midpoint-exceptional primes;
* arbitrarily large primes in the class `p ≡ 1 [MOD 5]`;
* fresh eligible starts outside any finite set of prime starts;
* generic descent from a cofinal tail reaches below a moving bound `B`;
* generic descent alone is too weak, since every odd prime has the trivial
  descent edge through `2`;
* row divisors of the left and right quadratic rows force `5` to be a square
  modulo the divisor.

The missing theorem is not "fresh starts". It is "fresh/distinct MP/PM events".

## Two Candidate Proof Routes

### Route A: Fixed Window Plus Tail-Shift Induction

Statement shape:

```text
base overflow in [0,A]
+ for every B,n there exists n' such that
  events inferred from [B+1,B+n'] recover or exceed
  events inferred from [B,B+n]
=> no cofinal exception tail.
```

Lean already has the abstract induction shell:

```lean
TailInductionCertificate.of_finitePrefixRecovery
exists_count_exceeds_of_eventual_increment
```

What remains is a concrete recovery theorem. The local audit data says this
route is plausible but collision-heavy:

```text
per-seed start>=191281 limit=30 cap=95568 predictedUniverse=264260
seed#1 p=191281 recursiveUnique=181052 freshVsPrior=181052
seed#2 p=191299 recursiveUnique=179564 freshVsPrior=9612
...
seed#17 p=191621 recursiveUnique=92962 freshVsPrior=2
seed#23 p=191791 recursiveUnique=145646 freshVsPrior=0
```

This shows inheritance is real, but fresh increments may be tiny or zero for
individual seeds. A proof must work with batches, not one seed at a time.

Fixed-window pressure would need one of:

* a batch-level lower bound on new distinct event images;
* an escape bound plus a finite-fiber/collision bound, using
  `exists_fresh_event_of_escape_and_fiber_bounds`;
* a residue-class theorem proving that infinitely many shifted tail starts
  produce event images outside the old fixed window set.

Weakness: this route fights the finite window. The more recursion we allow, the
more all seeds share common low descendants, and the audit shows huge overlap.

### Route B: Moving Window Finite Slots

Statement shape:

```text
For every B, [0,B) has finite MP/PM slots.
Cofinal exceptions after B supply infinitely many eligible split seeds.
Those seeds force enough distinct produced events in [0,B)
to exceed the finite slot count.
```

Lean endpoint:

```lean
arbitrarily_large_twins_of_movingWindowEventPressure
```

This is the cleaner target. It avoids tracking a single old finite block while
the tail start moves. It asks directly for distinct event pressure in the
window attached to the hypothetical tail start.

The main technical burden is:

```text
fresh eligible seeds + exceptional routing
=> enough distinct produced MP/PM events.
```

Generic descent cannot prove this because all odd primes may share the edge to
`2`. The route must use the event-producing quadratic rows, prewheeling, or a
finite-residue escape theorem.

## Experimental Facts

Commands were run from the reduced repository using:

```bash
g++ -std=c++17 -O2 -Wall -Wextra -pedantic \
  tools/audit_k2_forward.cpp -o tools/audit_k2_forward_wsl
```

### Scan of 200 split seeds

```text
scan start>=191281 seeds=200
minReach=92962 at 191621
maxReach=198502 at 195131
avgReach=171216
belowOrAtCap=1
maxGapBetweenUsableSeeds=118
```

Interpretation: almost every seed individually beats the finite cap, but this
is not proof because the finite cap and event universe are fixed and event
images collide.

### Bottom reach for 500 split seeds

```text
cutoff-reach start>=191281 seeds=500 noChild=0
maxBottom=31 atSeed=191281
cutoff<=31 hit=500 miss=0
bottom=31 count=500
```

Interpretation: descent reaching very low is empirically ubiquitous in this
model. But this does not imply fresh pressure, because all paths may share low
nodes.

### Event frequency for 500 split seeds

```text
event-frequency start>=191281 seeds=500 falseOnly=0 distinctEvents=230098
rank=1 eventId=12 u=568 side=0 freq=500 actual=1
...
```

False-only:

```text
event-frequency start>=191281 seeds=500 falseOnly=1 distinctEvents=146899
rank=1 eventId=2426 u=100798 side=0 freq=500 actual=0
...
```

Interpretation: event pressure is abundant, but collisions are also extreme.
This is why the endpoint should count distinct event union over a batch, not
raw descents and not terminal bottoms.

### Window batch test

```text
window start>=191281 seeds=500
w=1 minMax=55360 badWindowsByMax=2 minSum=55360
w=2 minMax=129380 badWindowsByMax=0 minSum=225646
```

Interpretation: any adjacent pair among the first 500 split seeds in this
range has enough maximum recursive unique pressure to exceed the 95568 cap.
This supports a finite-prefix recovery theorem, but the proof still needs a
batch event-realization and collision argument.

### Sliding distinct-union audit

The audit tool now has a `--window-union` mode, which measures the actual
distinct event union over consecutive batches of split seeds.  This is the
right finite statistic for the fixed-window recovery idea.

Near the generated threshold:

```text
window-union start>=191281 seeds=1000 cap=95568 predictedUniverse=264260
w=1 minUnion=50630 minUnionAtSeed#554 p=205171 badWindowsByUnion=5
w=2 minUnion=144508 minUnionAtSeed#397 p=201359 badWindowsByUnion=0
w=3 minUnion=166836 minUnionAtSeed#997 p=216371 badWindowsByUnion=0
```

Around `10^6`:

```text
window-union start>=1000000 seeds=200 cap=95568 predictedUniverse=264260
w=1 minUnion=92408 minUnionAtSeed#146 p=1003741 badWindowsByUnion=1
w=2 minUnion=160650 minUnionAtSeed#189 p=1005209 badWindowsByUnion=0
```

Around `10^7`:

```text
window-union start>=10000000 seeds=120 cap=95568 predictedUniverse=264260
w=1 minUnion=160210 minUnionAtSeed#31 p=10000871 badWindowsByUnion=0
w=2 minUnion=185302 minUnionAtSeed#31 p=10000871 badWindowsByUnion=0
```

Around `10^8`:

```text
window-union start>=100000000 seeds=100 cap=95568 predictedUniverse=264260
w=1 minUnion=145642 minUnionAtSeed#29 p=100001081 badWindowsByUnion=0
w=2 minUnion=189710 minUnionAtSeed#48 p=100001809 badWindowsByUnion=0
```

Interpretation: the one-seed statistic has rare misses near the threshold,
but adjacent pairs repair every miss in the sampled ranges.  This is strong
evidence for the fixed-window successor-recovery theorem in a small-batch
form:

```text
when shifting the tail start loses one split seed, adjoining finitely many
new split seeds recovers enough distinct event union to overflow the cap.
```

The missing proof is not ordinary monotonicity.  It is a proof that these
small batches cannot all keep landing inside an old finite event image.

### Common low sinks are not enough

The same audit shows why "descent reaches a low prime" is too weak:

```text
bad-child start>=191281 seeds=500 target=31
summary bad=0 good=500 noChild=0 maxMinReachedParent=31
```

Every sampled seed reaches `31`, and explicit paths show many different
descent chains collapsing to the same low sink.  This agrees with the Lean
guardrail theorem:

```lean
odd_prime_has_two_descent_edge
```

Generic descent cannot prove MP/PM pressure.  The proof must count distinct
side-events along the recursive rows, or else prove a residue-escape theorem
for finite event sinks.

### Recursive raw multiplicity is large

The local `K <= 2` intuition should not be used as a global recursive
multiplicity theorem.  Direct targets have no collisions in the tested ranges,
but unrestricted recursive raw paths have very large fibers:

```text
range=[191281,192000] splitPrimeStarts=31
direct raw=158 unique=158 maxFiber=1 fibersGt2=0
recursive raw=235282630 unique=213038 maxFiber=7472 fibersGt2=200604

range=[198000,199000] splitPrimeStarts=42
direct raw=232 unique=232 maxFiber=1 fibersGt2=0
recursive raw=368212716 unique=215544 maxFiber=11681 fibersGt2=204012

range=[1000000,1001000] splitPrimeStarts=39
direct raw=34 unique=34 maxFiber=1 fibersGt2=0
recursive raw=733558422 unique=220608 maxFiber=23262 fibersGt2=210442
```

Interpretation: `K <= 2` remains useful as a local algebraic edge bound or as
a depth-bounded composition budget, but it cannot close the recursive pressure
law by itself.  The observed phenomenon is not low multiplicity; it is that
the distinct union is still huge despite the multiplicity.

### Tail-shift recovery audit

The `--recovery-seeds` mode directly tests the shifted-tail idea.  For a
prefix of `k` consecutive eligible split seeds, it compares:

* the old distinct event union from seeds `i .. i+k-1`;
* the shifted union after shedding the first seed, `i+1 .. i+k-1`;
* the number of extra seeds needed to recover the old union count;
* the number of extra seeds needed merely to remain above the cap.

Near the generated threshold:

```text
recovery start>=191281 seeds=120 maxExtra=30
prefix=1 minOld=92962 maxExtraOldCount=9 maxExtraCap=2
prefix=2 minOld=158302 minShift=92962 maxExtraOldCount=8 maxExtraCap=1
prefix=3 minOld=170918 minShift=158302 maxExtraOldCount=8 maxExtraCap=0
prefix=5 minOld=180074 minShift=174168 maxExtraOldCount=8 maxExtraCap=0
prefix=10 minOld=197752 minShift=194114 maxExtraOldCount=8 maxExtraCap=0
```

Around `10^6`:

```text
recovery start>=1000000 seeds=100 maxExtra=30
prefix=1 minOld=125124 maxExtraOldCount=6 maxExtraCap=1
prefix=2 minOld=167736 minShift=125124 maxExtraOldCount=7 maxExtraCap=0
prefix=3 minOld=179706 minShift=167736 maxExtraOldCount=6 maxExtraCap=0
```

Around `10^7`:

```text
recovery start>=10000000 seeds=80 maxExtra=30
prefix=1 minOld=160210 maxExtraOldCount=7 maxExtraCap=1
prefix=2 minOld=185302 minShift=160210 maxExtraOldCount=6 maxExtraCap=0
prefix=3 minOld=193418 minShift=185302 maxExtraOldCount=9 maxExtraCap=0
```

Around `10^8`:

```text
recovery start>=100000000 seeds=100 maxExtra=50
prefix=1 minOld=145642 maxExtraOldCount=7 maxExtraCap=1
prefix=2 minOld=189710 minShift=145642 maxExtraOldCount=6 maxExtraCap=0
prefix=3 minOld=194960 minShift=189710 maxExtraOldCount=7 maxExtraCap=0
```

Interpretation: high multiplicity works in our favor for tail-shifting.
Shedding the first seed loses only a modest number of distinct events once the
prefix has two or three seeds.  A realistic successor theorem could use a
fixed small batch rather than arbitrary long recovery:

```text
every sufficiently late adjacent pair of eligible split seeds has recursive
event-union above the cap,
```

with a finite initial certificate near the threshold.  Then shifting a
three-seed prefix loses at most the first seed and leaves an adjacent-pair
overflow behind.

### Exact lost-event recovery

The stricter audit asks whether the precise events lost by deleting the first
seed reappear later, not just whether the count or cap overflow is recovered.
This is a different theorem.  It corresponds to:

```lean
exists_exact_recovery_batch_after_shift
```

which is now formalized in `TwinPrimeCertificate.DescentPressure`: if every
lost event has a later ancestor seed, then one finite extension recovers all
lost events at once.

Empirically, exact recurrence can be much slower than count recovery:

```text
recover-one start>=191281 index=1 prefix=3 lost=9988 maxExtra=2000
extra=353 seed=200329 remainingLost=0

recover-one start>=191281 index=18 prefix=3 lost=1344 maxExtra=2000
extra=2000 seed=241249 remainingLost=4
remaining events: u=4189726 side=0/1, u=7286728 side=0/1
```

So exact-event recovery is plausible for some windows, but it is not a small
constant phenomenon.  The theorem needed to close it is the ascent/multiplicity
statement:

```text
each lost event has arbitrarily late eligible split-prime ancestors.
```

Once that is proved, finite exact recovery follows immediately by the Lean
finite-choice/max argument.  Without that ascent theorem, exact recurrence is
empirically slower than ordinary overflow recovery and should not be assumed
from aggregate multiplicity alone.

### Multiplicity-two recovery theorem

The weakest exact-recovery bridge is now formal:

```lean
exists_shifted_seed_of_multiplicity_two
oldEvents_subset_shifted_of_removed_events_multiplicity_two
oldEvents_subset_shifted_union_later_of_multiplicity_two
lostEvents_have_later_eligible_ancestors_of_multiplicity_two
exists_exact_eligible_recovery_batch_after_shift
```

These theorems say exactly what the tail-shift argument needs:

```text
if every event produced by the removed seed has multiplicity at least two
after adding the shifted/later seeds, then deleting that seed loses no events.
```

The second pair says:

```text
if every lost event has, after any bound, a finite eligible split-seed batch
where that event appears with multiplicity at least two, then every lost event
has arbitrarily late eligible ancestors, and one finite eligible recovery batch
recovers the whole shifted prefix.
```

So the remaining arithmetic theorem can be stated in the weakest possible
form:

```text
for every event lost by the shift, there exists a later eligible split seed
that produces the same event.
```

Equivalently, every relevant lost event has recursive multiplicity at least
two after a finite extension.

Important limitation: direct parents of a fixed event are finite, because a
direct parent prime must divide one fixed quadratic row value.  The observed
high multiplicity is recursive.  Proving it arithmetically means proving that
some smaller split child has arbitrarily large split-prime parents through the
row construction.  For a fixed child `q`, slot `s`, and row polynomial `Q`,
this asks for arbitrarily large split primes `p` whose legal row root `u`
satisfies:

```text
Q(u) ≡ 0 mod p,
u ≡ -s mod q,
1 ≤ Q(u)/p < p.
```

That is a quadratic-root residue-class supply theorem, not ordinary
monotonicity.  It is exactly the kind of input supplied by DFI/Tóth-style
equidistribution of roots of quadratic congruences to prime moduli.

## Relevant Literature

### Quadratic roots modulo primes

Duke, Friedlander, and Iwaniec proved equidistribution of roots of quadratic
congruences to prime moduli; the Annals page identifies the paper as
"Equidistribution of roots of a quadratic congruence to prime moduli", Annals
of Mathematics 141 (1995), 423-441.

Source: <https://annals.math.princeton.edu/1995/141-2/p08>

Toth's "Roots of quadratic congruences", IMRN 2000, states that as the modulus
runs through primes, roots of a quadratic congruence are uniformly distributed
in a natural sense, building on DFI.

Source: <https://academic.oup.com/imrn/article-pdf/2000/14/719/1939261/2000-14-719.pdf>

Ngo's 2021 paper improves estimates for positive discriminants and explicitly
frames the DFI/Toth theorem as an effective Weyl-linear-form problem.

Source: <https://arxiv.org/abs/2107.13301>

Use in our problem:

* Let `E` be a finite sink of MP/PM events.
* Reverse the sink to a finite bad set of row-root residues modulo `M`.
* DFI/Toth/Ngo-style equidistribution can supply infinitely many split primes
  whose quadratic row root avoids the bad set and lies in a legal height range.
* If exceptional, such a seed must force a new event or descend beyond the
  certified depth.

This is the best analytic route to a finite-sink escape theorem.

### Covering systems and interval covers

Hough proved that the least modulus of a distinct covering system is bounded
by `10^16`. This is relevant because a terminal exception tail creates a family
of reciprocal residue classes that attempts to cover all candidate indices.

Source: <https://annals.math.princeton.edu/2015/181-1/p06>

Balister, Bollobas, Morris, Sahasrabudhe, and Tiba proved that if `k`
arithmetic progressions cover `2^k` consecutive numbers, then they cover all
integers. They also note that if the sum of reciprocal moduli is less than
one, then no interval of length `2^k` is covered.

Source: <https://digitalcommons.memphis.edu/facpubs/4474/>

Use in our problem:

* Prewheel by small primes so only high-prime reciprocal classes can cover.
* A finite prefix of high-prime classes covering a long interval would imply a
  global or density-heavy cover.
* If the reciprocal sum of relevant high-prime moduli is too small, interval
  cover is impossible.

This may prove a survivor directly, bypassing MP/PM pressure.

### Larger sieve

Gallagher's larger sieve controls sets contained in few residue classes modulo
many primes. It is relevant in the contrapositive direction: if all candidates
are killed by high-prime reciprocal classes, the surviving set is forced into
too few classes across many moduli.

Source: <https://ecroot.math.gatech.edu/gallagher.pdf>

Use in our problem:

* Candidate hard-to-kill prewheeled `m` values avoid small primes.
* Each high prime removes or covers only two reciprocal classes.
* Larger-sieve estimates may upper-bound the size of a complete high-prime
  cover or force a residue escape.

This is likely useful for a prewheel survivor theorem, less directly for
MP/PM finite-slot overflow.

## Most Promising Lemmas

### Lemma 1: finite bad-root escape

For any finite sink-induced bad residue set `Bad ⊂ Z/MZ`, there are
arbitrarily large split primes `p` and legal row roots `u` such that:

```text
Q(u) ≡ 0 mod p,
u mod M ∉ Bad,
1 ≤ Q(u)/p < p.
```

This is the DFI/Toth/Ngo route. It directly supports:

```lean
ResidueFiniteSinkAvoidanceCertificate.escaping_root_after
```

Difficulty: analytic number theory, not currently in mathlib.

### Lemma 2: batch distinct-event pressure

For every moving window `slots B` and bound `N`, there are finitely many
eligible split seeds `p > N` whose produced event union has cardinality greater
than `slots B`.

This is exactly:

```lean
MovingWindowEventPressureCertificate.distinct_event_pressure
```

Difficulty: must control event collisions. Experiments support it strongly,
but generic descent does not prove it.

### Lemma 3: fixed-window successor recovery

Given a base overflowing finite certificate in `[0,A]`, shifting the tail start
from `B` to `B+1` loses at most the events tied only to the removed seed, and
some finite lengthening supplies at least as many new distinct events.

This supports:

```lean
GeneratedFinitePrefixRecoveryCertificate.recover
```

Difficulty: also a distinct-event/collision theorem. A single new seed can add
zero fresh events, so the proof must use batches.

### Lemma 4: prewheeled high-prime non-cover

For `W = product_{p≤w} p`, a future exception must cover an interval of
prewheeled candidates using only primes `q > w`. Prove this high-prime
reciprocal cover cannot be complete for sufficiently large `r,w`.

This may bypass MP/PM entirely.

Difficulty: resembles covering systems/larger sieve. It may be the most
mathematically standard route, but it is farther from the current Lean endpoint.

## Recommendation

Focus on Route B with Lemma 1 or Lemma 2.

Route A is useful as a finite audit and may still close with a batch theorem,
but it keeps fighting collisions in a fixed universe. Route B says the right
thing: every hypothetical tail start has only finitely many slots below it, and
the cofinal tail must produce more distinct MP/PM events than those slots can
hold.

The next concrete task is to formalize a finite-residue bad-set model:

```lean
structure BadRootResidueModel where
  modulus : Nat
  bad : Finset Nat
  bad_not_total : bad.card < modulus
  route_into_sink_iff_bad :
    ...
```

Then the exact external analytic/computational theorem becomes:

```lean
∀ M Bad, Bad ≠ all residues ->
  ∀ N, ∃ p u, N < p ∧ ModFiveOnePrime p ∧
    rowRoot p u ∧ u % M ∉ Bad ∧ legalHeight p u
```

This is precise enough to ask a mathematician about, to test computationally,
or to isolate as the next Lean theorem if a suitable source theorem is found.

## DFI/Toth root-supply status

I checked the local mathlib checkout and the relevant public sources.  Mathlib
contains Dirichlet's theorem in arithmetic progressions, plus the special
theorem giving arbitrarily large primes `p ≡ 1 mod k`, but it does not contain
the Duke--Friedlander--Iwaniec / Toth theorem on equidistribution of roots of
quadratic congruences to prime moduli.

The literature match is exact:

* Duke, Friedlander, and Iwaniec, *Equidistribution of roots of a quadratic
  congruence to prime moduli*, Annals of Mathematics 141 (1995), 423--441.
* Toth, *Roots of quadratic congruences*, IMRN 2000, 719--739.
* Ngo, *On roots of quadratic congruences*, arXiv:2107.13301, strengthens the
  Weyl-form estimates for positive discriminants.

For our row polynomials

```text
L(u) = u(u+3)+1,
R(u) = (u+1)(u+4)+1,
```

both discriminants are `5`.  The required corollary is much weaker than a full
asymptotic theorem:

```text
For each finite event e, with its row side, modulus M_e, and allowed root
residue a_e, and for every N, there is p > N and a legal root u such that

  p is prime,
  p ≡ 1 (mod 5),
  Q_e(u) = p h with 1 ≤ h < p,
  u ≡ a_e (mod M_e),
  and the generated descent checker records e ∈ ProducedEvents(p).
```

The new Lean file `TwinPrimeCertificate/QuadraticRootSupply.lean` formalizes
exactly what this corollary buys us:

```lean
EventParentSupply
QuadraticRootParentSupply
multiplicity_two_after_of_eventParentSupply
exists_exact_eligible_recovery_batch_after_shift_of_eventParentSupply
exists_exact_eligible_recovery_batch_after_shift_of_quadraticRootSupply
```

This proves in Lean that arbitrarily-late one-parent supply for each lost event
is already enough.  Request one parent after `N`, then another parent after the
first one; the two distinct parents give the multiplicity-two batch required by
the existing exact recovery theorem.

So the remaining analytic theorem has been narrowed to `root_after` in
`QuadraticRootParentSupply`.  Plain Dirichlet is not enough for that field:
Dirichlet controls the residue class of the prime `p`, while `root_after` must
also control a root `u` of a quadratic congruence modulo `p`, its residue modulo
the event modulus, and a legal-height interval condition.  That is precisely
the DFI/Toth root-equidistribution input.
