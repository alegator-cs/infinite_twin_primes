import TwinPrimeCertificate.Final
import TwinPrimeCertificate.FiniteSinkAvoidance

/-!
# Direct Unique-Descent Endpoint

This is the lightweight endpoint for the no-certificate route.  It deliberately
does not import the generated routed-chain shards.

The required mathematical input is the direct moving-window uniqueness theorem:
for each eligible exceptional seed `p` above a tail start `B`, a chosen terminal
event is produced in the finite window `slots B`, and that terminal event
records `p` among its finite ancestors.  Lean then uses Dirichlet's theorem for
primes `p ≡ 1 [MOD 5]` to choose an eligible exceptional seed outside the finite
ancestor union, contradiction.
-/

namespace TwinPrimeCertificate.UniqueDescentEndpoint

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

/-!
## Injective endpoint

This is the most direct "unique descents" surface.  It does not mention
ancestor sets: terminal events must land in the finite moving window and be
injective on eligible exceptional seeds above the same tail start.
-/

def fromInjectiveMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_injective :
      forall B p q,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                B < q ->
                  threshold < q ->
                    ModFiveOnePrime q ->
                      MidpointExceptionalPrime q ->
                        terminalEvent B p = terminalEvent B q ->
                          p = q) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_injectiveMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_injective)

theorem no_cofinalExceptionTail_of_injectiveMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_injective :
      forall B p q,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                B < q ->
                  threshold < q ->
                    ModFiveOnePrime q ->
                      MidpointExceptionalPrime q ->
                        terminalEvent B p = terminalEvent B q ->
                          p = q) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromInjectiveMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_injective)

theorem arbitrarily_large_twins_of_injectiveMovingWindowDescent
    {threshold : Nat}
    {slots : Nat -> Finset Nat}
    (terminalEvent : Nat -> Nat -> Nat)
    (terminalEvent_in_window :
      forall B p,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                terminalEvent B p ∈ slots B)
    (terminalEvent_injective :
      forall B p q,
        B < p ->
          threshold < p ->
            ModFiveOnePrime p ->
              MidpointExceptionalPrime p ->
                B < q ->
                  threshold < q ->
                    ModFiveOnePrime q ->
                      MidpointExceptionalPrime q ->
                        terminalEvent B p = terminalEvent B q ->
                          p = q) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromInjectiveMovingWindowDescent
      terminalEvent terminalEvent_in_window terminalEvent_injective)

/-!
## Event-pressure endpoint

This exposes the set-valued version where every valid MP/PM event encountered
along a descent may count.  It requires distinct event pressure directly,
rather than injectivity of seed-to-terminal-event.
-/

def fromMovingWindowEventPressure
    (cert : TwinPrimeCertificate.MovingWindowEventPressureCertificate) :
    MidpointTailInductionCertificate :=
  TailInductionCertificate.of_no_cofinalTail
    certificateVerifiedTo
    (TwinPrimeCertificate.no_cofinalExceptionTail_of_movingWindowEventPressure cert)

theorem no_cofinalExceptionTail_of_movingWindowEventPressure
    (cert : TwinPrimeCertificate.MovingWindowEventPressureCertificate) :
    Not (exists B,
      CofinalExceptionTail MidpointExceptionalPrime B) :=
  TwinPrimeCertificate.no_cofinalExceptionTail
    (fromMovingWindowEventPressure cert)

theorem arbitrarily_large_twins_of_movingWindowEventPressure
    (cert : TwinPrimeCertificate.MovingWindowEventPressureCertificate) :
    ArbitrarilyLargeTwins :=
  TwinPrimeCertificate.arbitrarily_large_twins
    (fromMovingWindowEventPressure cert)

end TwinPrimeCertificate.UniqueDescentEndpoint
