import Integration7.ConstantCoefficientIntegralPresentations

/-! Replacing a family by its actual density graph also preserves the
chosen integral after multiplication by a constant positive coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}

theorem selected_coefficient_field_appended_integral_densityGraph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F) =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilyLeftProduct U F.densityGraph) := by
  apply selected_family_field_appended_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
  intro x
  let D := vfParameterVolumeContext C x
  let e := (RVVolumeIso.refl hc D (positiveVolumeCoefficientInContext U x)).prod hc D (F.densityGraphRowIso hc x)
  exact VolumeBlowupEquivalent.of_iso D
    ((selectedVolumeFamilyLeftProductRowIso hc U F x).trans hc D
      (e.trans hc D ((selectedVolumeFamilyLeftProductRowIso hc U F.densityGraph x).symm hc D)))
end IntegrationInACVF.Section7
