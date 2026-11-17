module

public import Integration7.PreparedPairFamilyAllOrderComparisons
public import Integration7.RVGraphRefinementContractionComparisons
public import Integration7.GeneratedBaseStandardContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The whole balanced graph-family case of Lemma7.7. Both prepared
keys are introduced by an actual RV graph refinement; its matching and
different comparisons are assembled before returning to the original
specified contractions and retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 3600000 in
theorem balanced_graph_family_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ) (hGenerated : VFGammaGeneratedBase G)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    {A : DefSet (M := M) (C.base : Set M) 2 m}
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin (m+F.arity))
    (hδ : ∀ p : gammaRVGraphRefinement A F.parameters hNames, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) σ)
    (W : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let H := gammaRVGraphRefinement A F.parameters hNames
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfinH δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC H hH hfinH δ hδ W hW) := by
  intro H hH hfinH hsmall
  obtain ⟨P⟩ := uniform_balanced_position_preparation_exists C hGC hNames γ hγ hγ1 F hBalanced
  let Q := P.inFixedContext
  have hPair := Q.whole_prepared_pair_family_gamma
  obtain ⟨R,hR,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hsmall hGenerated hGC
    Q.wholePreparedPairFamily hPair σ
  obtain ⟨S,hS,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hsmall hGenerated hGC
    Q.wholePreparedPairFamily hPair τ
  have hε := rv_graph_refinement_density_nonzero H Q.pairKeyLabels hNames δ hδ
  have hMiddle := UniformBalancedPositionPreparation.whole_prepared_pair_contractions_compare hc hGC hgamma
    γ hγ hγ1 hGeneric P hNonzero hfin
    (Fin.castAdd ((1+Q.sourceArity)+(1+Q.targetArity)) δ) hε R S hR hS
  have hLeft := rv_graph_refinement_contraction_common_blowup hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hNames hGeneric H hH hfinH Q.pairKeyLabels δ hδ T R hT hR
  have hRight := rv_graph_refinement_contraction_common_blowup hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hNames hGeneric H hH hfinH Q.pairKeyLabels δ hδ W S hW hS
  exact CommonContextVolumeEquivalent.trans hc hLeft
    (CommonContextVolumeEquivalent.trans hc hMiddle (CommonContextVolumeEquivalent.symm hc hRight))

end IntegrationInACVF.Section7.UniformMixedCellPresentation
