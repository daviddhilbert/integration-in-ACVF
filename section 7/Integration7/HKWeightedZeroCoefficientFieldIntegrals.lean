import Integration7.HKNativeZeroCoefficientFieldIntegrals
import Integration7.HKZeroRVNativeDensityPresentations
import Integration7.FieldBaseAppendedIntegralIndependence
import Integration7.ConstantCoefficientIntegralPresentations

/-! The chosen field-base integral commutes with every actual weighted
zero coefficient, not only coordinate-density representatives. Exact
row comparisons justify both density-graph reductions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (FBase : VFFieldBase (C.base : Set M))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
include hΞ hNames γ hγ hγ1

theorem retained_family_field_appended_integral_weighted_zero_coefficient
    (F : SelectedVFVolumeFamily C 1 a k) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedFamilyWeightedZeroProduct F Z) =
      rvVolumeBlowupClass hc C (n := 0) Z • selectedFamilyFieldAppendedIntegral hc C Ξ FBase F := by
  let V := zeroRVNativeDensityObject hc C Z
  have hZ : rvVolumeBlowupClass hc C (n := 0) Z = rvVolumeBlowupClass hc C (n := 0) V :=
    Quotient.sound ⟨zeroRVNativeDensityIso hc C Z⟩
  have hCompare := selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
    (selectedFamilyWeightedZeroProduct F Z) (selectedFamilyWeightedZeroProduct F V) (by
      intro x
      apply (positiveVolumeBlowupClass_eq_iff hc _).mp
      rw [selected_family_weighted_zero_row_scalar,selected_family_weighted_zero_row_scalar,hZ])
  exact hCompare.trans ((native_zero_coefficient_field_appended_integral hc C Ξ hΞ FBase hNames γ hγ hγ1
    F δ hF hδ (zeroRVNativeDensityDomain hc C Z) (Fin.last Z.underlying.obj.arity)
    (ordinary_rv_native_labels_finite hc C Z.densityGraph.underlying) (zero_rv_native_density_nonzero hc C Z)).trans
      (congrArg (fun z => z • selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) hZ.symm))

theorem selected_family_field_appended_integral_weighted_zero_coefficient
    (F : SelectedVFVolumeFamily C 1 a k)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedFamilyWeightedZeroProduct F Z) =
      rvVolumeBlowupClass hc C (n := 0) Z • selectedFamilyFieldAppendedIntegral hc C Ξ FBase F := by
  have hCompare := selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
    (selectedFamilyWeightedZeroProduct F Z) (selectedFamilyWeightedZeroProduct F.densityGraph Z) (by
      intro x
      apply (positiveVolumeBlowupClass_eq_iff hc _).mp
      rw [selected_family_weighted_zero_row_scalar,selected_family_weighted_zero_row_scalar,
        positiveVolumeBlowupClass_iso hc _ (F.densityGraphRowIso hc x)])
  exact hCompare.trans ((retained_family_field_appended_integral_weighted_zero_coefficient hc C Ξ hΞ FBase hNames γ hγ hγ1
    F.densityGraph (Fin.last a) F.densityGraph_form_last F.densityGraph_label_nonzero Z).trans
      (congrArg (fun v => rvVolumeBlowupClass hc C (n := 0) Z • v)
        (selected_family_field_appended_integral_densityGraph hc C Ξ hΞ FBase hNames γ hγ hγ1 F).symm))

end IntegrationInACVF.Section7.HK
