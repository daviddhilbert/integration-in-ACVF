import Integration7.TwoCellContractionReduction
import Integration7.GeneratedBaseStandardContractions
import Integration7.VolumeContextJoins

/-! Two specified contractions in arbitrary orders reduce simultaneously
to actual contractions of the same cell family. Both comparison chains
are realized in one genuine containing context over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}

set_option maxHeartbeats 1600000 in
theorem two_order_cell_family_reduction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) 2 a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program) :
    let hreal : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    ∃ d : ℕ, ∃ P : GammaRVMap B (carrier A) d,
      ParameterizedCells.DefinableTwoCell B (carrier (gammaRVGraphRefinement A P hNames)) ∧
      let H := gammaRVGraphRefinement A P hNames
      let hH := gamma_rv_graph_refinement_target_gamma A P hNames
      let hfinH := gamma_rv_graph_refinement_finite_labels A hfin P hNames
      let hε := rv_graph_refinement_density_nonzero A P hNames δ hδ
      ∃ E : StandardContraction H σ, ∃ L : StandardContraction H τ,
      ∃ hE : GammaProgramDefinable B E.program, ∃ hL : GammaProgramDefinable B L.program,
      let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC A hA hfin δ hδ T hT
      let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC A hA hfin δ hδ W hW
      let X := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC H hH hfinH (Fin.castAdd d δ) hε E hE
      let Y := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hBC H hH hfinH (Fin.castAdd d δ) hε L hL
      ∃ (K : BaseContext M) (hCK : (C.base : Set M) ⊆ (K.base : Set M)),
        GammaVolumeBlowupEquivalent B (K.base : Set M) 1 (U.extend hCK) (X.extend hCK) ∧
        GammaVolumeBlowupEquivalent B (K.base : Set M) 1 (V.extend hCK) (Y.extend hCK) := by
  intro hreal
  obtain ⟨d,P,hCell,hCompare⟩ := two_cell_contraction_reduction hc C hBC hNames hgamma hGenerated γ hγ hγ1
    hGeneric A hA hfin δ hδ
  let H := gammaRVGraphRefinement A P hNames
  have hH := gamma_rv_graph_refinement_target_gamma A P hNames
  obtain ⟨E,hE,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hreal hGenerated hBC H hH σ
  obtain ⟨L,hL,_⟩ := generated_base_standard_contraction_exists C.saturated C.model00 hreal hGenerated hBC H hH τ
  obtain ⟨KE,hCKE,hTE⟩ := hCompare σ T E hT hE
  obtain ⟨KL,hCKL,hWL⟩ := hCompare τ W L hW hL
  obtain ⟨K,hEK,hLK⟩ := volume_context_join_exists KE KL
  exact ⟨d,P,hCell,E,L,hE,hL,K,hCKE.trans hEK,hTE.extend hEK,hWL.extend hLK⟩

end IntegrationInACVF.Section7
