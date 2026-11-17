module

public import Integration7.MatchingContractionPreparedVolumes
public import Integration7.MatchingPreparedVolumeComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The two actual translated matching families have the full common
forward Gamma volume-blowup comparison for arbitrary specified orders.
The middle comparison is the actual prepared-family volume isomorphism. -/
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
theorem matching_translated_contractions_compare
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
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction (extendBase P.inFixedContext.matchingVerticalImage P.inFixedContext.baseInclusion) σ)
    (W : StandardContraction (extendBase P.inFixedContext.matchingHorizontalImage P.inFixedContext.baseInclusion) τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let Q := P.inFixedContext
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH := Q.matching_prepared_family_finite_labels hfin
    let hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    let hfinW := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    let hδV := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 0 Q.matchingVerticalCentre δ hδ
    let hδW := relative_translation_retained_density_nonzero Q.matchingPreparedFamily 1 Q.matchingHorizontalCentre δ hδ
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingVerticalImage Q.baseInclusion) Q.matching_vertical_image_gamma hfinV δ hδV T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hGC
        (extendBase Q.matchingHorizontalImage Q.baseInclusion) Q.matching_horizontal_image_gamma hfinW δ hδW W hW) := by
  intro Q hsmall hfinH hfinV hfinW hδV hδW
  obtain ⟨LV,LH,e,he⟩ := matching_prepared_volume_comparison hc hGC P γ hγ1 hNonzero hfin δ hδ
  let PV := Q.matchingVerticalPullbackPreparation hNonzero LV
  let PH := Q.matchingHorizontalPullbackPreparation hNonzero LH
  have hAF := PV.finite_volume C.uncountable.le C.saturated hsmall
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
  have hBF := PH.finite_volume C.uncountable.le C.saturated hsmall
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
  have hεV := PV.retained_density_nonzero P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matching_fixed_vertical_labels δ hδ
  have hεW := PH.retained_density_nonzero P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_horizontal_labels δ hδ
  let U := pullbackCoordinateGammaObject hc C hGC PV.volumeTarget PV.volume_target_gamma hAF (PV.volumeLabelIndex δ) hεV
  let V := pullbackCoordinateGammaObject hc C hGC PH.volumeTarget PH.volume_target_gamma hBF (PH.volumeLabelIndex δ) hεW
  have hMiddle : CommonContextVolumeEquivalent G C U V := CommonContextVolumeEquivalent.of_iso e he
  have hLeft := matching_vertical_contraction_to_prepared_volume hc hGC hgamma γ hγ hγ1 hGeneric
    P hNonzero hfin δ hδ LV T hT
  have hRight := matching_horizontal_contraction_to_prepared_volume hc hGC hgamma γ hγ hγ1 hGeneric
    P hNonzero hfin δ hδ LH W hW
  exact CommonContextVolumeEquivalent.trans hc hLeft
    (CommonContextVolumeEquivalent.trans hc hMiddle (CommonContextVolumeEquivalent.symm hc hRight))

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
