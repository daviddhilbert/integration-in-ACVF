module

public import Integration7.UniformCellVerticalContractions
public import Integration7.UniformBalancedHorizontalContractions
public import Integration7.MixedTranslationContractionComparisons
public import Integration7.RVGraphRefinementContractionComparisons

@[expose] public section

/-! Specified contractions of the actual cell family reduce to
constructed contractions of its two uniform translations. The comparison
chains retain the original Gamma base and the literal old density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 1600000 in
theorem vertical_contraction_reduction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) 2 m)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (F : UniformMixedCellPresentation G (carrier A)) (δ : Fin m)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) (Equiv.refl _))
    (hT : GammaProgramDefinable G T.program) :
    let hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let H := gammaRVGraphRefinement A F.parameters hNames
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    let hε := rv_graph_refinement_density_nonzero A F.parameters hNames δ hδ
    let Y := F.verticalTranslationImage hNames
    let hY := F.vertical_translation_image_gamma hNames
    let hfinY := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hreal
      (F.verticalTranslation hNames) (F.vertical_translation_bijective hNames)
      (F.vertical_translation_graph_gamma hNames) hfinH
    let hζ := relative_translation_retained_density_nonzero H 0 (F.refinementCentreMap hNames) (Fin.castAdd F.arity δ) hε
    let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC H hH hfinH
      (Fin.castAdd F.arity δ) hε T hT
    ∃ E : StandardContraction Y (Equiv.refl _), ∃ hE : GammaProgramDefinable G E.program,
      let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Y hY hfinY
        (Fin.castAdd F.arity δ) hζ E hE
      ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
        GammaVolumeBlowupEquivalent G (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro hreal H hH hfinH hε Y hY hfinY hζ U
  obtain ⟨E,hE⟩ := F.vertical_translation_standard_contraction_exists C hNames γ hγ hγ1
  exact ⟨E,hE,mixed_translation_contraction_common_blowup hc C C.uncountable.le C.saturated
    hreal hgamma γ hγ hγ1 hGC hGeneric H hH hfinH 0 (F.refinementCentreMap hNames)
    (F.refinement_centre_constant hNames) (F.refinement_centre_gamma hNames)
    (Fin.castAdd F.arity δ) hε rfl T E hT hE⟩

set_option maxHeartbeats 1600000 in
theorem horizontal_contraction_reduction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) 2 m)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (F : UniformMixedCellPresentation G (carrier A)) (hBalanced : F.BalancedRows) (δ : Fin m)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (T : StandardContraction (gammaRVGraphRefinement A F.parameters hNames) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable G T.program) :
    let hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let H := gammaRVGraphRefinement A F.parameters hNames
    let hH := gamma_rv_graph_refinement_target_gamma A F.parameters hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames
    let hε := rv_graph_refinement_density_nonzero A F.parameters hNames δ hδ
    let Y := F.horizontalTranslationImage hBalanced hNames
    let hY := F.horizontal_translation_image_gamma hBalanced hNames
    let hfinY := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hreal
      (F.horizontalTranslation hBalanced hNames) (F.horizontal_translation_bijective hBalanced hNames)
      (F.horizontal_translation_graph_gamma hBalanced hNames) hfinH
    let hζ := relative_translation_retained_density_nonzero H 1 (F.horizontalCentreMap hBalanced hNames) (Fin.castAdd F.arity δ) hε
    let U := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC H hH hfinH
      (Fin.castAdd F.arity δ) hε T hT
    ∃ E : StandardContraction Y (Equiv.swap 0 1), ∃ hE : GammaProgramDefinable G E.program,
      let V := retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Y hY hfinY
        (Fin.castAdd F.arity δ) hζ E hE
      ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
        GammaVolumeBlowupEquivalent G (D.base : Set M) 1 (U.extend hCD) (V.extend hCD) := by
  intro hreal H hH hfinH hε Y hY hfinY hζ U
  obtain ⟨E,hE⟩ := F.horizontal_translation_standard_contraction_exists C hNames γ hγ hγ1 hBalanced
  exact ⟨E,hE,mixed_translation_contraction_common_blowup hc C C.uncountable.le C.saturated
    hreal hgamma γ hγ hγ1 hGC hGeneric H hH hfinH 1 (F.horizontalCentreMap hBalanced hNames)
    (F.horizontal_centre_constant hBalanced hNames) (F.horizontal_centre_graph_gamma hBalanced hNames)
    (Fin.castAdd F.arity δ) hε (by decide) T E hT hE⟩

end IntegrationInACVF.Section7.UniformMixedCellPresentation
