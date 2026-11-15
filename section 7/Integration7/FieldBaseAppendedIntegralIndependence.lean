import Integration7.FieldBaseAppendedIntegralAdditivity

/-! The fixed additive coordinate normalization transports the actual
field-base comparison to coefficient-first appended integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_field_appended_integral_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase F =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase G := by
  apply (canonicalFromAppendedVolumeAddEquiv hc C n k).injective
  rw [selected_family_field_integral_from_appended,selected_family_field_integral_from_appended]
  exact selected_family_field_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1 F G hCommon
end IntegrationInACVF.Section7
