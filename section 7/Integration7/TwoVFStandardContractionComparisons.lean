module

public import Integration7.UniformCellGraphFamilyComparison
public import Integration7.RVGraphRefinementContractionComparisons
public import Integration7.GeneratedBaseStandardContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full VF-two case of Lemma7.7: arbitrary specified standard
contractions in any two orders, with arbitrary retained nonzero density,
have common forward volume blowups over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {a : ℕ}

set_option maxHeartbeats 3600000 in
theorem two_vf_standard_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ) (hGenerated : VFGammaGeneratedBase G)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) 2 a) (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC A hA hfin δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC A hA hfin δ hδ W hW) := by
  intro hsmall
  obtain ⟨F⟩ := uniform_mixed_cell_presentation_exists C.uncountable.le C.saturated C.model00 hsmall
    hGenerated γ hγ hγ1 hA
  let H := gammaRVGraphRefinement A F.parameters hNames
  have hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
  obtain ⟨R,hR,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hsmall hGenerated hGC H hH σ
  obtain ⟨S,hS,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hsmall hGenerated hGC H hH τ
  have hε := rv_graph_refinement_density_nonzero A F.parameters hNames δ hδ
  have hMiddle := F.graph_family_contractions_compare hc C hGC hNames hgamma hGenerated
    γ hγ hγ1 hGeneric hfin (Fin.castAdd F.arity δ) hε R S hR hS
  have hLeft := rv_graph_refinement_contraction_common_blowup hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hNames hGeneric A hA hfin F.parameters δ hδ T R hT hR
  have hRight := rv_graph_refinement_contraction_common_blowup hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hNames hGeneric A hA hfin F.parameters δ hδ W S hW hS
  exact CommonContextVolumeEquivalent.trans hc hLeft
    (CommonContextVolumeEquivalent.trans hc hMiddle (CommonContextVolumeEquivalent.symm hc hRight))

end IntegrationInACVF.Section7
