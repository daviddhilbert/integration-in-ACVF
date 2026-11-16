module

public import Integration7.PreparedPairContractionRestrictions
public import Integration7.StandardBinaryRestrictionVolumePartitions
public import Integration7.MatchingFamilyAllOrderComparisons

@[expose] public section

/-! Matching and different prepared-ball cases assemble into the
whole balanced pair-key refinement. All specified contraction orders
and arbitrary retained nonzero densities are compared. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

set_option maxHeartbeats 4000000 in
theorem whole_prepared_pair_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))
    (hδ : ∀ p : P.inFixedContext.wholePreparedPairFamily, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction P.inFixedContext.wholePreparedPairFamily σ)
    (W : StandardContraction P.inFixedContext.wholePreparedPairFamily τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let Q := P.inFixedContext
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.whole_prepared_pair_family_finite_labels hfin
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma hfinH δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma hfinH δ hδ W hW) := by
  intro Q hsmall hfinH
  obtain ⟨MT⟩ := Q.matching_pair_contraction_presentation T hT
  obtain ⟨DT⟩ := Q.different_pair_contraction_presentation T hT
  obtain ⟨MW⟩ := Q.matching_pair_contraction_presentation W hW
  obtain ⟨DW⟩ := Q.different_pair_contraction_presentation W hW
  have hfinM := Q.matching_prepared_family_finite_labels hfin
  have hfinD := Q.different_prepared_family_finite_labels hfin
  have hδM : ∀ p : Q.matchingPreparedFamily, (p.val.2 δ).val ≠ iRVZero :=
    fun p => hδ ⟨p.val,Q.matching_prepared_subset_whole p.property⟩
  have hδD : ∀ p : Q.differentPreparedFamily, (p.val.2 δ).val ≠ iRVZero :=
    fun p => hδ ⟨p.val,Q.different_prepared_subset_whole p.property⟩
  let XT := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma hfinH δ hδ T hT
  let XW := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.wholePreparedPairFamily Q.whole_prepared_pair_family_gamma hfinH δ hδ W hW
  let YT := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.matchingPreparedFamily Q.matching_prepared_family_gamma hfinM δ hδM MT.contraction MT.gamma
  let ZT := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.differentPreparedFamily Q.different_prepared_family_gamma hfinD δ hδD DT.contraction DT.gamma
  let YW := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.matchingPreparedFamily Q.matching_prepared_family_gamma hfinM δ hδM MW.contraction MW.gamma
  let ZW := retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
    Q.differentPreparedFamily Q.different_prepared_family_gamma hfinD δ hδD DW.contraction DW.gamma
  obtain ⟨eT,heT⟩ := standard_binary_restriction_volume_partition C.uncountable.le C.saturated hsmall hc C hGC
    Q.wholePreparedPairFamily Q.matchingPreparedFamily Q.differentPreparedFamily
    Q.whole_prepared_pair_family_gamma Q.matching_prepared_family_gamma Q.different_prepared_family_gamma
    hfinH hfinM hfinD id Q.matchingPreparedRVLabels Q.matching_prepared_rv_labels_gamma
    Q.different_prepared_rv_labels_gamma hNames T hT MT DT δ hδ hδM hδD
  obtain ⟨eW,heW⟩ := standard_binary_restriction_volume_partition C.uncountable.le C.saturated hsmall hc C hGC
    Q.wholePreparedPairFamily Q.matchingPreparedFamily Q.differentPreparedFamily
    Q.whole_prepared_pair_family_gamma Q.matching_prepared_family_gamma Q.different_prepared_family_gamma
    hfinH hfinM hfinD id Q.matchingPreparedRVLabels Q.matching_prepared_rv_labels_gamma
    Q.different_prepared_rv_labels_gamma hNames W hW MW DW δ hδ hδM hδD
  have hPartitionT : CommonContextVolumeEquivalent G C (YT.coprod ZT) XT := .of_iso eT heT
  have hPartitionW : CommonContextVolumeEquivalent G C (YW.coprod ZW) XW := .of_iso eW heW
  have hMatch : CommonContextVolumeEquivalent G C YT YW :=
    matching_family_contractions_compare hc hGC hgamma γ hγ hγ1 hGeneric P hNonzero hfin δ hδM
      MT.contraction MW.contraction MT.gamma MW.gamma
  have hDifferent : CommonContextVolumeEquivalent G C ZT ZW :=
    different_prepared_family_contractions_compare hc hgamma γ hγ hγ1 hGC hGeneric Q hfin δ hδD
      DT.contraction DW.contraction DT.gamma DW.gamma
  exact (hPartitionT.symm hc).trans hc ((hMatch.coprod hc hDifferent).trans hc hPartitionW)

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
