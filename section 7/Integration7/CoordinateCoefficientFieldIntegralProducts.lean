import Integration7.CoordinateCoefficientContractionProductCharts
import Integration7.SelectedRetainedContractionIntegrals
import Integration7.FieldBaseUnarySpecialPreparations
import Integration7.PositiveVolumeClassExtensions

/-! The actual chosen field-base appended integral commutes with a
literal-coordinate positive constant coefficient when the fibre density
is retained. The special preparations and product chart are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a d k p : ℕ}

set_option maxHeartbeats 1600000 in
theorem native_coefficient_field_appended_integral_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C 1 a k) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (R : DefSet (M := M) (C.base : Set M) 0 d) (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M),
      {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε) =
      rvVolumeBlowupClassesProduct hc C (p+1) ((k+1)+1)
        (positiveVolumeBlowupClass hc C (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε))
        (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) := by
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc F.domain)
  obtain ⟨L⟩ := native_coordinate_coefficient_special_preparation_exists hc C F R σ ε hR hε Ξ hNames δ hF T hT hB
  let J := nativeCoordinateCoefficientFamily hc C F R σ ε hR hε
  let U := nativeCoordinateDensityVolumeObject hc C R σ ε hR hε
  let V := unaryPreparedHeadVolumeObject hc C Ξ T hB hT F.selected δ hδ F.finite_selected
  have hIntegralF := selected_family_field_appended_integral_retained_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1
    F δ hF hδ (unarySpecialStandardContraction T hB)
  have hHeadF : positiveVolumeBlowupClass hc C V=selectedFamilyFieldAppendedIntegral hc C Ξ FBase F :=
    (hIntegralF.trans (positiveVolumeBlowupClass_iso hc C
      (unaryPreparedHeadVolumeIso hc C Ξ T hB hT F.selected δ hδ F.finite_selected))).symm
  calc
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase J =
        positiveVolumeBlowupClass hc C (J.standardAppendObject hc Ξ (unarySpecialStandardContraction L.special L.pullback)) :=
      selected_family_field_appended_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 J _
    _ = positiveVolumeBlowupClass hc C (U.prod V) :=
      positiveVolumeBlowupClass_iso hc C
        (coordinateCoefficientContractionProductIso hc C Ξ hNames F R σ ε hR hε δ hδ T hB hT L)
    _ = rvVolumeBlowupClassesProduct hc C (p+1) ((k+1)+1)
        (positiveVolumeBlowupClass hc C U) (positiveVolumeBlowupClass hc C V) := rfl
    _ = _ := by rw [hHeadF]
end IntegrationInACVF.Section7
