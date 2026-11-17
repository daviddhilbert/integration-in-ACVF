module

public import Integration7.HKZeroCoefficientContractionProductCharts
public import Integration7.SelectedRetainedContractionIntegrals
public import Integration7.FieldBaseUnarySpecialPreparations
public import Integration7.HKZeroCoefficientScalarRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Finite weighted zero coefficients commute with the chosen unary
field-base integral, with exact product densities before normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a d k : ℕ}

theorem weighted_zero_smul_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C U =
      positiveVolumeBlowupClass hc C (zeroProduct Z U) :=
  (zero_volume_coefficient_smul_eq_right_product hc C _ _).trans
    (positiveVolumeBlowupClass_iso hc C
      ((productPositiveZeroIso hc C U Z).trans hc C (mixedProductSwapIso hc C U Z)))

set_option maxHeartbeats 1600000 in
theorem native_zero_coefficient_field_appended_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C 1 a k) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (R : DefSet (M := M) (C.base : Set M) 0 d) (ε : Fin d)
    (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (nativeZeroCoefficientFamily hc C F R ε hR hε) =
      rvVolumeBlowupClass hc C (n := 0) (nativeZeroDensityObject hc C R ε hR hε) •
        selectedFamilyFieldAppendedIntegral hc C Ξ FBase F := by
  obtain ⟨b,B,T,hT,hB⟩ := field_base_unary_special_preparation C Ξ FBase (nativeMixedVolumeDomain hc F.domain)
  obtain ⟨L⟩ := native_zero_coefficient_special_preparation_exists hc C F R ε hR hε Ξ hNames δ hF T hT hB
  let J := nativeZeroCoefficientFamily hc C F R ε hR hε
  let Z := nativeZeroDensityObject hc C R ε hR hε
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
    _ = positiveVolumeBlowupClass hc C (zeroProduct Z V) :=
      positiveVolumeBlowupClass_iso hc C
        (zeroCoefficientContractionProductIso hc C Ξ hNames F R ε hR hε δ hδ T hB hT L)
    _ = rvVolumeBlowupClass hc C (n := 0) Z • positiveVolumeBlowupClass hc C V :=
      (weighted_zero_smul_representative hc C Z V).symm
    _ = _ := by rw [hHeadF]

end IntegrationInACVF.Section7.HK
