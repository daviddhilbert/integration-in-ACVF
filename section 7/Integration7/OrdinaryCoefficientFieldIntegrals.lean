import Integration7.OrdinaryCoefficientContractionProductCharts
import Integration7.SelectedRetainedContractionIntegrals
import Integration7.FieldBaseUnarySpecialPreparations
import Integration7.ConstantCoefficientIntegralPresentations
import Integration7.PositiveVolumeProductOrdinaryScalars
import Integration7.OrdinaryVolumeCoefficientScalarRows

/-! The chosen field-base integral commutes with actual ordinary RV[0]
coefficients on every positive selected family, before normalization.
The finite coefficient is retained by a genuine product preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

set_option maxHeartbeats 1600000 in
theorem retained_family_field_appended_integral_ordinary_coefficient
    (F : SelectedVFVolumeFamily C 1 a k) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (F.prodZero Z) =
      rvVolumeBlowupClass hc C (n := 0) Z • selectedFamilyFieldAppendedIntegral hc C Ξ FBase F := by
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc F.domain)
  obtain ⟨L⟩ := ordinary_coefficient_special_preparation_exists hc C Ξ hNames F Z T hT hB
  let J := F.prodZero Z
  let δJ := Fin.castAdd Z.obj.arity δ
  let hδJ := fun q hq => ordinary_coefficient_retained_density_nonzero C F Z δ hδ ⟨q,hq⟩
  have hFormJ (q : J.domain) : J.form.value q=q.val.2 δJ := by
    rw [SelectedVFVolumeFamily.prodZero_density,hF]
    exact congrArg (fun p => p.2 δ) (F.prodZeroProjection_value Z q)
  let Z₀ := nativeOrdinaryRVObject hc C (ordinaryRVNativeDomain hc C Z) (ordinary_rv_native_labels_finite hc C Z)
  let V := unaryPreparedHeadVolumeObject hc C Ξ T hB hT F.selected δ hδ F.finite_selected
  have hVF : selectedFamilyFieldAppendedIntegral hc C Ξ FBase F=positiveVolumeBlowupClass hc C V :=
    (selected_family_field_appended_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 F δ hF hδ
      (unarySpecialStandardContraction T hB)).trans
      (positiveVolumeBlowupClass_iso hc C (unaryPreparedHeadVolumeIso hc C Ξ T hB hT F.selected δ hδ F.finite_selected))
  calc
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase J = positiveVolumeBlowupClass hc C
        (standardAppendVolumeObject hc C Ξ (nativeMixedVolumeDomain hc J.domain) J.selected δJ hδJ J.finite_selected
          (unarySpecialStandardContraction L.special L.pullback)) :=
      selected_family_field_appended_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 J δJ hFormJ hδJ _
    _ = positiveVolumeBlowupClass hc C (PositiveRVVolumeObject.zero_prod Z₀ V) :=
      positiveVolumeBlowupClass_iso hc C (ordinaryCoefficientContractionProductIso hc C Ξ hNames F Z δ hδ T hB hT L)
    _ = positiveVolumeBlowupClass hc C (V.prod_zero Z₀) :=
      (positiveVolumeBlowupClass_iso hc C (volumeZeroProductSwapIso hc C V Z₀)).symm
    _ = rvVolumeBlowupClass hc C (n := 0) Z₀ • positiveVolumeBlowupClass hc C V :=
      (ordinary_volume_smul_representative hc C Z₀ V).symm
    _ = _ := by rw [ordinary_rv_native_class,← hVF]

theorem selected_family_field_appended_integral_ordinary_coefficient
    (F : SelectedVFVolumeFamily C 1 a k)
    (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (F.prodZero Z) =
      rvVolumeBlowupClass hc C (n := 0) Z • selectedFamilyFieldAppendedIntegral hc C Ξ FBase F := by
  have hCompare := selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
    (F.prodZero Z) (F.densityGraph.prodZero Z) (by
      intro x
      apply (positiveVolumeBlowupClass_eq_iff hc _).mp
      rw [volume_family_zero_product_row_scalar,volume_family_zero_product_row_scalar,
        positiveVolumeBlowupClass_iso hc _ (F.densityGraphRowIso hc x)])
  exact hCompare.trans ((retained_family_field_appended_integral_ordinary_coefficient hc C Ξ hΞ FBase hNames γ hγ hγ1
    F.densityGraph (Fin.last a) F.densityGraph_form_last F.densityGraph_label_nonzero Z).trans
      (congrArg (fun v => rvVolumeBlowupClass hc C (n := 0) Z • v)
        (selected_family_field_appended_integral_densityGraph hc C Ξ hΞ FBase hNames γ hγ hγ1 F).symm))
end IntegrationInACVF.Section7
