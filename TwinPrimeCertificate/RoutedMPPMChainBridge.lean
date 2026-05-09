import TwinPrimeCertificate.RecursiveMPPMCertificate
import TwinPrimeCertificate.GeneratedRoutedMPPMChains.Index

/-!
# Bridge from Checked Recursive MP/PM Route Chains

The generated routed-chain shards check 95,569 explicit recursive descent
witnesses.  Each witness contains:

* a start split prime;
* concrete quadratic row equations;
* concrete decreasing descended-prime edges, with divisibility quotients;
* a terminal encoded MP/PM side event.

This bridge uses the checked chain count as the predicted MP/PM event set in
the existing finite-cardinality contradiction.
-/

namespace TwinPrimeCertificate

open TwinPrimeCertificate.RoutedMPPMChainCertificate

theorem routed_checkedChainCount_exceeds_generatedMPPMCard :
    generatedMPPMCard <
      GeneratedRoutedMPPMChains.checkedChainCount := by
  rw [GeneratedRoutedMPPMChains.checkedChainCount_eq]
  norm_num [generatedMPPMCard]

def routedChainActualEvents : Finset Nat :=
  Finset.range generatedMPPMCard

theorem routedChainActualEvents_card :
    routedChainActualEvents.card = generatedMPPMCard := by
  simp [routedChainActualEvents]

def routedChainPredictedEvents : Finset Nat :=
  Finset.range GeneratedRoutedMPPMChains.checkedChainCount

theorem routedChainPredictedEvents_card :
    routedChainPredictedEvents.card =
      GeneratedRoutedMPPMChains.checkedChainCount := by
  simp [routedChainPredictedEvents]

theorem routedChainPredictedEvents_card_eq :
    routedChainPredictedEvents.card = 95569 := by
  rw [routedChainPredictedEvents_card]
  exact GeneratedRoutedMPPMChains.checkedChainCount_eq

theorem routedChainActualEvents_card_eq :
    routedChainActualEvents.card = 95568 := by
  rw [routedChainActualEvents_card]
  norm_num [generatedMPPMCard]

theorem routedChainPredicted_card_exceeds_actual :
    routedChainActualEvents.card < routedChainPredictedEvents.card := by
  rw [routedChainActualEvents_card_eq, routedChainPredictedEvents_card_eq]
  norm_num

theorem cofinalTail_before_certificatePrefix_forces_generatedSeed
    {B : Nat}
    (tail : CofinalExceptionTail MidpointExceptionalPrime B)
    (hB : B < certificatePrefixStart) :
    MidpointExceptionalPrime certificateFirstSplitPrime := by
  simpa [certificatePrefixStart] using
    cofinalTail_forces_certificateFirstSplitPrime tail hB

theorem certificateVerifiedTo_lt_certificatePrefixStart :
    certificateVerifiedTo < certificatePrefixStart := by
  norm_num [certificateVerifiedTo, certificatePrefixStart,
    certificateFirstSplitPrime]

theorem cofinalTail_certificateVerifiedTo_forces_generatedSeed
    (tail : CofinalExceptionTail MidpointExceptionalPrime certificateVerifiedTo) :
    MidpointExceptionalPrime certificateFirstSplitPrime :=
  cofinalTail_before_certificatePrefix_forces_generatedSeed tail
    certificateVerifiedTo_lt_certificatePrefixStart

/--
If a checked shard says all its chains start inside the certificate prefix,
then any member chain starts at the concrete certificate seed.  The current
certificate prefix is the singleton `[certificateFirstSplitPrime,
certificateFirstSplitPrime]`.
-/
theorem chain_start_eq_certificateFirst_of_mem_allStartsIn
    {chains : List ChainWitness}
    {chain : ChainWitness}
    (hstarts :
      allStartsIn certificatePrefixStart certificatePrefixEnd chains = true)
    (hmem : chain ∈ chains) :
    chain.start = certificateFirstSplitPrime := by
  have hchain :
      ((certificatePrefixStart <= chain.start) &&
          (chain.start <= certificatePrefixEnd)) = true :=
    (List.all_eq_true.mp hstarts) chain hmem
  have hbounds :
      certificatePrefixStart <= chain.start ∧
        chain.start <= certificatePrefixEnd := by
    have hbool := (Bool.and_eq_true
      (certificatePrefixStart <= chain.start)
      (chain.start <= certificatePrefixEnd)).mp hchain
    exact ⟨of_decide_eq_true hbool.1, of_decide_eq_true hbool.2⟩
  norm_num [certificatePrefixStart, certificatePrefixEnd,
    certificateFirstSplitPrime] at hbounds ⊢
  omega

/--
Specific seed-realization bridge for the generated prefix certificate:
under a cofinal exceptional tail beginning before the certificate prefix, every
checked chain in any shard whose starts are checked in that prefix has an
exceptional start.
-/
theorem chain_start_exceptional_of_cofinalTail_before_prefix
    {B : Nat}
    {chains : List ChainWitness}
    {chain : ChainWitness}
    (tail : CofinalExceptionTail MidpointExceptionalPrime B)
    (hB : B < certificatePrefixStart)
    (hstarts :
      allStartsIn certificatePrefixStart certificatePrefixEnd chains = true)
    (hmem : chain ∈ chains) :
    MidpointExceptionalPrime chain.start := by
  have hstart :
      chain.start = certificateFirstSplitPrime :=
    chain_start_eq_certificateFirst_of_mem_allStartsIn hstarts hmem
  simpa [hstart] using
    cofinalTail_before_certificatePrefix_forces_generatedSeed tail hB

theorem chain_start_exceptional_of_cofinalTail_certificateVerifiedTo
    {chains : List ChainWitness}
    {chain : ChainWitness}
    (tail : CofinalExceptionTail MidpointExceptionalPrime certificateVerifiedTo)
    (hstarts :
      allStartsIn certificatePrefixStart certificatePrefixEnd chains = true)
    (hmem : chain ∈ chains) :
    MidpointExceptionalPrime chain.start :=
  chain_start_exceptional_of_cofinalTail_before_prefix tail
    certificateVerifiedTo_lt_certificatePrefixStart hstarts hmem

/--
Base-case semantic realization certificate for the generated route chains.

The generated shards check the arithmetic of the selected recursive descent
chains.  This base-case field is exactly the remaining interpretation theorem
needed to turn a cofinal exceptional tail beginning at `certificateVerifiedTo`
into real MP/PM pressure in the finite target block.
-/
structure RoutedBaseCaseRealizationCertificate where
  realized_of_tail_after_certificate :
    CofinalExceptionTail MidpointExceptionalPrime certificateVerifiedTo ->
      ∀ event, event ∈ routedChainPredictedEvents ->
        event ∈ routedChainActualEvents

theorem cofinalTailContradicts_certificateVerifiedTo_of_routedBaseCaseCertificate
    (cert : RoutedBaseCaseRealizationCertificate) :
    CofinalTailContradicts MidpointExceptionalPrime certificateVerifiedTo := by
  intro tail
  have hle :
      routedChainPredictedEvents.card <= routedChainActualEvents.card :=
    Finset.card_le_card (by
      intro event hevent
      exact cert.realized_of_tail_after_certificate tail event hevent)
  have hgt :
      routedChainActualEvents.card < routedChainPredictedEvents.card :=
    routedChainPredicted_card_exceeds_actual
  omega

end TwinPrimeCertificate
