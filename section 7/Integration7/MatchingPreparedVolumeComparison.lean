module

public import Integration7.MatchingFixedContextVolumeMaps
public import Integration7.GammaPreparedRectangleVolumeComparison

@[expose] public section

/-! Actual full volume comparison of the prepared matching family.
Both recorded-key preparations are constructed, every finiteness,
nonzero-coordinate and label-determination obligation is discharged,
and the resulting RV volume isomorphism retains the original Gamma base.
The density is any nonzero retained family label. -/
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
theorem matching_prepared_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    (hNonzero : ∀ a : A, (F.vertical.projection a).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin ((m+F.arity)+((1+P.inFixedContext.sourceArity)+(1+P.inFixedContext.targetArity))))
    (hδ : ∀ p : P.inFixedContext.matchingPreparedFamily, (p.val.2 δ).val ≠ iRVZero) :
    let Q := P.inFixedContext
    ∃ LV : PreparedKeyLabelSpecialPreparation Q.sourceSpecial
      (extendBase Q.matchingVerticalTailDomain Q.baseInclusion) Q.matchingOldLabelIndex Q.matchingTailKeyIndex
      (fun p hp => Q.matching_vertical_tail_old_mem ⟨p,hp⟩) G,
    ∃ LH : PreparedKeyLabelSpecialPreparation Q.targetSpecial
      (extendBase Q.matchingHorizontalHeadDomain Q.baseInclusion) Q.matchingOldLabelIndex Q.matchingHeadKeyIndex
      (fun p hp => Q.matching_horizontal_head_old_mem ⟨p,hp⟩) G,
    let PV := Q.matchingVerticalPullbackPreparation hNonzero LV
    let PH := Q.matchingHorizontalPullbackPreparation hNonzero LH
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hfinH : ∀ x : Fin 2 → VF (M := M),
      {r | (x,r) ∈ carrier (extendBase Q.matchingPreparedFamily Q.baseInclusion)}.Finite :=
        Q.matching_prepared_family_finite_labels hfin
    let hδH : ∀ p : extendBase Q.matchingPreparedFamily Q.baseInclusion,
      (p.val.2 δ).val ≠ iRVZero := hδ
    let hAF := PV.finite_volume C.uncountable.le C.saturated hsmall
      P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective P.matching_fixed_vertical_gamma hfinH
    let hBF := PH.finite_volume C.uncountable.le C.saturated hsmall
      P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_gamma hfinH
    let hδV := PV.retained_density_nonzero P.matchingFixedVerticalMap
      P.matching_fixed_vertical_bijective P.matching_fixed_vertical_labels δ hδH
    let hδW := PH.retained_density_nonzero P.matchingFixedHorizontalMap
      P.matching_fixed_horizontal_bijective P.matching_fixed_horizontal_labels δ hδH
    ∃ e : RVVolumeIso
      (pullbackCoordinateVolumeObject hc PV.volumeTarget hAF (PV.volumeLabelIndex δ) hδV)
      (pullbackCoordinateVolumeObject hc PH.volumeTarget hBF (PH.volumeLabelIndex δ) hδW),
      e.GammaDefinable G := by
  intro Q
  obtain ⟨LV⟩ := Q.matching_vertical_recorded_preparation_exists
  obtain ⟨LH⟩ := Q.matching_horizontal_recorded_preparation_exists
  refine ⟨LV,LH,?_⟩
  intro PV PH hsmall hfinH hδH hAF hBF hδV hδW
  let e := RectangleFamilyPullbackPreparation.volumeIsoOfConjugate hc C hGC PV PH
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_vertical_gamma P.matching_fixed_horizontal_gamma
    P.matching_fixed_vertical_labels P.matching_fixed_horizontal_labels
    (P.matching_fixed_vertical_jacobian_one hc) (P.matching_fixed_horizontal_jacobian_one hc)
    hfinH δ hδH
    (Q.matching_vertical_prepared_labels_determine hNonzero LV)
    (Q.matching_horizontal_prepared_labels_determine hNonzero LH)
    (Q.matching_vertical_prepared_nonzero γ hγ hNonzero LV)
    (Q.matching_horizontal_prepared_nonzero γ hγ hNonzero LH)
  exact ⟨e,RectangleFamilyPullbackPreparation.volumeIsoOfConjugate_gamma hc C hGC PV PH
    P.matchingFixedVerticalMap P.matching_fixed_vertical_bijective
    P.matchingFixedHorizontalMap P.matching_fixed_horizontal_bijective
    P.matching_fixed_vertical_gamma P.matching_fixed_horizontal_gamma
    P.matching_fixed_vertical_labels P.matching_fixed_horizontal_labels
    (P.matching_fixed_vertical_jacobian_one hc) (P.matching_fixed_horizontal_jacobian_one hc)
    hfinH δ hδH
    (Q.matching_vertical_prepared_labels_determine hNonzero LV)
    (Q.matching_horizontal_prepared_labels_determine hNonzero LH)
    (Q.matching_vertical_prepared_nonzero γ hγ hNonzero LV)
    (Q.matching_horizontal_prepared_nonzero γ hγ hNonzero LH)⟩

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
