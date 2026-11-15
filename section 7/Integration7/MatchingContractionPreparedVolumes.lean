import Integration7.MatchingFixedContextVolumeMaps
import Integration7.MatchingPreparedUnaryRelative
import Integration7.LabelDeterminedPullbackRectangles
import Integration7.RectanglePullbackVolumeConnections
import Integration7.PreparedRectangleFiniteVolumes
import Integration7.MixedTranslationContractionComparisons

/-! Each actual translated matching-family contraction compares to
its constructed prepared pullback volume object, in every specified
VF-two order and with arbitrary retained density. -/
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

set_option maxHeartbeats 3000000 in
theorem matching_vertical_contraction_to_prepared_volume
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
    (L : PreparedKeyLabelSpecialPreparation P.inFixedContext.sourceSpecial
      (extendBase P.inFixedContext.matchingVerticalTailDomain P.inFixedContext.baseInclusion)
      P.inFixedContext.matchingOldLabelIndex P.inFixedContext.matchingTailKeyIndex
      (fun p hp => P.inFixedContext.matching_vertical_tail_old_mem ⟨p,hp⟩) G)
    {σ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingVerticalImage P.inFixedContext.baseInclusion) σ)
    (hT : GammaProgramDefinable G T.program) :
    let Q := P.inFixedContext
    let PV := Q.matchingVerticalPullbackPreparation hNonzero L
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    let hδV := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 0 Q.matchingVerticalCentre δ hδ
    let hAF := PV.finite_volume C.uncountable.le C.saturated hsmall
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    let hε := PV.retained_density_nonzero P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
      P.matching_fixed_vertical_labels δ hδ
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingVerticalImage Q.baseInclusion) Q.matching_vertical_image_gamma hfinV δ hδV T hT)
      (pullbackCoordinateGammaObject hc C hGC PV.volumeTarget PV.volume_target_gamma hAF (PV.volumeLabelIndex δ) hε) := by
  intro Q PV hsmall hfinH hfinV hδV hAF hε
  have hfinA := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    (Map.comp PV.volumeMap P.matchingFixedVerticalMap)
    (PV.volume_map_bijective.comp P.matching_fixed_vertical_bijective)
    (gamma_composition_graph _ _ P.matching_fixed_vertical_gamma PV.volume_graph_gamma) hfinH
  exact rectangle_contraction_to_pullback_volume hc C hgamma γ hγ hγ1 hGC hNames hGeneric
    (extendBase Q.matchingVerticalImage Q.baseInclusion) PV.volumeTarget
    Q.matching_vertical_image_gamma PV.volume_target_gamma hfinV hfinA
    (Q.matching_vertical_image_rectangular hNonzero)
    (Q.matching_vertical_prepared_rectangular hNonzero L) PV.volume_target_pullback hAF
    δ (PV.volumeLabelIndex δ) hδV hε PV.volumeMap PV.volume_map_bijective PV.volume_graph_gamma
    (fun p => PV.volume_old_labels p δ) (PV.volume_jacobian_one hc C)
    (Equiv.swap 0 1) (Q.matching_vertical_prepared_unary_relative hNonzero L) T hT

set_option maxHeartbeats 3000000 in
theorem matching_horizontal_contraction_to_prepared_volume
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
    (L : PreparedKeyLabelSpecialPreparation P.inFixedContext.targetSpecial
      (extendBase P.inFixedContext.matchingHorizontalHeadDomain P.inFixedContext.baseInclusion)
      P.inFixedContext.matchingOldLabelIndex P.inFixedContext.matchingHeadKeyIndex
      (fun p hp => P.inFixedContext.matching_horizontal_head_old_mem ⟨p,hp⟩) G)
    {σ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingHorizontalImage P.inFixedContext.baseInclusion) σ)
    (hT : GammaProgramDefinable G T.program) :
    let Q := P.inFixedContext
    let PV := Q.matchingHorizontalPullbackPreparation hNonzero L
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    let hδV := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 1 Q.matchingHorizontalCentre δ hδ
    let hAF := PV.finite_volume C.uncountable.le C.saturated hsmall
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    let hε := PV.retained_density_nonzero P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
      P.matching_fixed_horizontal_labels δ hδ
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingHorizontalImage Q.baseInclusion) Q.matching_horizontal_image_gamma hfinV δ hδV T hT)
      (pullbackCoordinateGammaObject hc C hGC PV.volumeTarget PV.volume_target_gamma hAF (PV.volumeLabelIndex δ) hε) := by
  intro Q PV hsmall hfinH hfinV hδV hAF hε
  have hfinA := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    (Map.comp PV.volumeMap P.matchingFixedHorizontalMap)
    (PV.volume_map_bijective.comp P.matching_fixed_horizontal_bijective)
    (gamma_composition_graph _ _ P.matching_fixed_horizontal_gamma PV.volume_graph_gamma) hfinH
  exact rectangle_contraction_to_pullback_volume hc C hgamma γ hγ hγ1 hGC hNames hGeneric
    (extendBase Q.matchingHorizontalImage Q.baseInclusion) PV.volumeTarget
    Q.matching_horizontal_image_gamma PV.volume_target_gamma hfinV hfinA
    (Q.matching_horizontal_image_rectangular hNonzero)
    (Q.matching_horizontal_prepared_rectangular hNonzero L) PV.volume_target_pullback hAF
    δ (PV.volumeLabelIndex δ) hδV hε PV.volumeMap PV.volume_map_bijective PV.volume_graph_gamma
    (fun p => PV.volume_old_labels p δ) (PV.volume_jacobian_one hc C)
    (Equiv.refl _) (Q.matching_horizontal_prepared_unary_relative hNonzero L) T hT

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
