import TwinPrimeCertificate.Final
import TwinPrimeCertificate.RoutedMPPMChainBridge
import TwinPrimeCertificate.FiniteSinkAvoidance

/-!
# Generated Tail-Induction Certificate Wiring

This file connects the generated MP/PM overflow certificates to the final
tail-induction endpoint.

The preferred certificate surface is now the finite-prefix/successor recovery
surface below.  It separates the concrete base overflow at
`certificateVerifiedTo` from the shifted-tail successor recovery theorem.

The older `RoutedChainRealizationCertificate` endpoint remains available as a
compact compatibility wrapper.
-/

namespace TwinPrimeCertificate.GeneratedTailInductionCertificate

/--
Generated finite-prefix recovery certificate.

The base field is the concrete checked overflow at the certificate threshold.
The recovery field is the successor step of the shifted-tail argument: once a
tail after `B` is contradictory, advancing the threshold to `B + 1` can be
recovered after a finite prefix lengthening.  The exact length `C` is not part
of the public theorem.
-/
structure GeneratedFinitePrefixRecoveryCertificate where
  base : TwinPrimeCertificate.RoutedBaseCaseRealizationCertificate
  recover :
    ∀ B,
      certificateVerifiedTo <= B ->
        CofinalTailContradicts MidpointExceptionalPrime B ->
          ∃ C, B + 1 <= C /\
            ExceptionPrefix MidpointExceptionalPrime B C

/--
Same endpoint surface as `GeneratedFinitePrefixRecoveryCertificate`, but with
the successor contradiction supplied directly.  This is useful if the recovery
theorem is proved as a pressure monotonicity statement rather than literally as
an exceptional-prime prefix.
-/
structure GeneratedSuccessorRecoveryCertificate where
  base : TwinPrimeCertificate.RoutedBaseCaseRealizationCertificate
  successor_recovery :
    ∀ B,
      certificateVerifiedTo <= B ->
        CofinalTailContradicts MidpointExceptionalPrime B ->
          CofinalTailContradicts MidpointExceptionalPrime (B + 1)

def fromGeneratedFinitePrefixRecovery
    (cert : GeneratedFinitePrefixRecoveryCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_finitePrefixRecovery
    certificateVerifiedTo
    (cofinalTailContradicts_certificateVerifiedTo_of_routedBaseCaseCertificate
      cert.base)
    cert.recover

def fromGeneratedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    MidpointTailInductionCertificate where
  baseThreshold := certificateVerifiedTo
  base_contradiction :=
    cofinalTailContradicts_certificateVerifiedTo_of_routedBaseCaseCertificate
      cert.base
  successor_contradiction := cert.successor_recovery

theorem no_cofinalExceptionTail_of_generatedFinitePrefixRecovery
    (cert : GeneratedFinitePrefixRecoveryCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromGeneratedFinitePrefixRecovery cert)

theorem arbitrarily_large_twins_of_generatedFinitePrefixRecovery
    (cert : GeneratedFinitePrefixRecoveryCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromGeneratedFinitePrefixRecovery cert)

theorem no_cofinalExceptionTail_of_generatedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromGeneratedSuccessorRecovery cert)

theorem arbitrarily_large_twins_of_generatedSuccessorRecovery
    (cert : GeneratedSuccessorRecoveryCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromGeneratedSuccessorRecovery cert)

def fromRoutedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_routedMPPMChainCertificate cert)

theorem no_cofinalExceptionTail_of_routedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromRoutedChainRealization cert)

theorem arbitrarily_large_twins_of_routedChainRealization
    (cert : TwinPrimeCertificate.RoutedChainRealizationCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromRoutedChainRealization cert)

def fromModFiveSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveSeedOverflowCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_modFiveSeedOverflowCertificate cert)

theorem no_cofinalExceptionTail_of_modFiveSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveSeedOverflowCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromModFiveSeedOverflow cert)

theorem arbitrarily_large_twins_of_modFiveSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveSeedOverflowCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromModFiveSeedOverflow cert)

/--
Endpoint for the realistic mod-5 seed surface: the certificate only needs an
arbitrarily large good subfamily of primes `p ≡ 1 [MOD 5]`, not every such
prime.  Mathlib supplies arbitrarily large primes in the ambient residue class;
the certificate supplies the good subfamily and the generated MP/PM overflow
for each good seed.
-/
def fromModFiveGoodSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveGoodSeedOverflowCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_modFiveGoodSeedOverflowCertificate cert)

theorem no_cofinalExceptionTail_of_modFiveGoodSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveGoodSeedOverflowCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromModFiveGoodSeedOverflow cert)

theorem arbitrarily_large_twins_of_modFiveGoodSeedOverflow
    (cert : TwinPrimeCertificate.ModFiveGoodSeedOverflowCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromModFiveGoodSeedOverflow cert)

/--
Endpoint for the multiplicity-free terminal-slot sink formulation.

This is the clean finite-sink surface: a cofinal exceptional tail would force
all terminal events into one finite slot set, while the certificate supplies
arbitrarily late exceptional seeds forcing an event outside that set.
-/
def fromTerminalSlotSink
    (cert : TwinPrimeCertificate.TerminalSlotSinkCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_terminalSlotSink cert)

theorem no_cofinalExceptionTail_of_terminalSlotSink
    (cert : TwinPrimeCertificate.TerminalSlotSinkCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromTerminalSlotSink cert)

theorem arbitrarily_large_twins_of_terminalSlotSink
    (cert : TwinPrimeCertificate.TerminalSlotSinkCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromTerminalSlotSink cert)

/--
Endpoint for the ancestor-to-terminal-slot bridge.

This is the multiplicity-free version that uses the already-proved infinite
fresh eligible-prime supply: a finite slot set has a finite ancestor union, so
some later eligible exceptional seed lies outside that union.  If every
in-slot forced event records the seed as an ancestor, the forced event must
escape the slot set, contradicting terminal-slot absorption.
-/
def fromTerminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.TerminalSlotAncestorBridgeCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_terminalSlotAncestorBridge cert)

theorem no_cofinalExceptionTail_of_terminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.TerminalSlotAncestorBridgeCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromTerminalSlotAncestorBridge cert)

theorem arbitrarily_large_twins_of_terminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.TerminalSlotAncestorBridgeCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromTerminalSlotAncestorBridge cert)

/--
Endpoint for the moving terminal-window ancestor bridge.

Here the finite slot universe may depend on the hypothetical cofinal-tail start
`B`, matching the "take the whole window up to the tail start" formulation.
-/
def fromMovingTerminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.MovingTerminalSlotAncestorBridgeCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_movingTerminalSlotAncestorBridge cert)

theorem no_cofinalExceptionTail_of_movingTerminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.MovingTerminalSlotAncestorBridgeCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromMovingTerminalSlotAncestorBridge cert)

theorem arbitrarily_large_twins_of_movingTerminalSlotAncestorBridge
    (cert : TwinPrimeCertificate.MovingTerminalSlotAncestorBridgeCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromMovingTerminalSlotAncestorBridge cert)

/--
Endpoint for the direct unique moving-window descent theorem.

This is the no-count, no-certificate-record surface: once a concrete theorem
provides a chosen terminal event for every eligible exceptional seed, proves
that the event lands in the finite window attached to the tail start, and
proves that the landing records the seed as an ancestor, Lean rules out a
cofinal exceptional tail.
-/
def fromUniqueMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    {ancestorsOf : Nat -> Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_records_ancestor :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                p ∈ ancestorsOf B (terminalEvent B p)) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_uniqueMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_records_ancestor)

theorem no_cofinalExceptionTail_of_uniqueMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    {ancestorsOf : Nat -> Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_records_ancestor :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                p ∈ ancestorsOf B (terminalEvent B p)) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromUniqueMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_records_ancestor)

theorem arbitrarily_large_twins_of_uniqueMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    {ancestorsOf : Nat -> Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_records_ancestor :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                p ∈ ancestorsOf B (terminalEvent B p)) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromUniqueMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_records_ancestor)

end TwinPrimeCertificate.GeneratedTailInductionCertificate
