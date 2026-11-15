import Integration7.MatchingTranslatedContractionComparison

/-! Opposite specified contractions of the actual matching family
compare by their two relatively unary translations and the completed
full volume comparison of those translated families. -/
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

set_option maxHeartbeats 3600000 in
theorem matching_family_opposite_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))
    (hδ : ∀ p : P.inFixedContext.matchingPreparedFamily, (p.val.2 δ).val ≠ iRVZero)
    (T : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) (Equiv.refl _))
    (W : StandardContraction (extendBase P.inFixedContext.matchingPreparedFamily P.inFixedContext.baseInclusion) (Equiv.swap 0 1))
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let Q := P.inFixedContext
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingPreparedFamily Q.baseInclusion) Q.matching_prepared_family_gamma hfinH δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingPreparedFamily Q.baseInclusion) Q.matching_prepared_family_gamma hfinH δ hδ W hW) := by
  intro Q hsmall hfinH
  let H := extendBase Q.matchingPreparedFamily Q.baseInclusion
  let V := extendBase Q.matchingVerticalImage Q.baseInclusion
  let Y := extendBase Q.matchingHorizontalImage Q.baseInclusion
  have hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
  have hfinY := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
  have hδV := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 0 Q.matchingVerticalCentre δ hδ
  have hδY := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 1 Q.matchingHorizontalCentre δ hδ
  obtain ⟨R,hR⟩ := rectangle_family_contraction_in_order_exists C hNames γ hγ hγ1 V
    Q.matching_vertical_image_gamma (Q.matching_vertical_image_rectangular hNonzero) (Equiv.refl _)
  obtain ⟨S,hS⟩ := rectangle_family_contraction_in_order_exists C hNames γ hγ hγ1 Y
    Q.matching_horizontal_image_gamma (Q.matching_horizontal_image_rectangular hNonzero) (Equiv.swap 0 1)
  have hiV : UnaryRelative P.matchingFixedVerticalMap ((Equiv.refl (Fin 2)) 0) :=
    relative_translation_unary_relative Q.matchingPreparedFamily 0 Q.matchingVerticalCentre
  have hiY : UnaryRelative P.matchingFixedHorizontalMap ((Equiv.swap (0 : Fin 2) 1) 0) :=
    relative_translation_unary_relative Q.matchingPreparedFamily 1 Q.matchingHorizontalCentre
  have hLeft := retained_density_relative_contractions_compare hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hGeneric H V Q.matching_prepared_family_gamma Q.matching_vertical_image_gamma
    hfinH hfinV δ δ hδ hδV P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matching_fixed_vertical_gamma (fun _ => rfl) (P.matching_fixed_vertical_jacobian_one hc) hiV T R hT hR
  have hRight := retained_density_relative_contractions_compare hc C C.uncountable.le C.saturated hsmall
    hgamma γ hγ hγ1 hGC hGeneric H Y Q.matching_prepared_family_gamma Q.matching_horizontal_image_gamma
    hfinH hfinY δ δ hδ hδY P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_horizontal_gamma (fun _ => rfl) (P.matching_fixed_horizontal_jacobian_one hc) hiY W S hW hS
  have hMiddle := matching_translated_contractions_compare hc hGC hgamma γ hγ hγ1 hGeneric
    P hNonzero hfin δ hδ R S hR hS
  exact CommonContextVolumeEquivalent.trans hc hLeft
    (CommonContextVolumeEquivalent.trans hc hMiddle (CommonContextVolumeEquivalent.symm hc hRight))

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
