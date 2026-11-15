import Integration7.FieldBaseVolumeIntegralPartitions
import Integration7.SelectedSumLabelCutRowIsomorphisms

/-! Additivity of the actual chosen integral over an arbitrary VF field
base. The old-tag partition of one contraction supplies both summands. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_field_canonical_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k) :
    selectedFamilyFieldCanonicalIntegral hc C Ξ FBase (selectedVolumeFamilySum F G) =
      selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F + selectedFamilyFieldCanonicalIntegral hc C Ξ FBase G := by
  have hL := selected_family_field_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
    (selectedSumLeftCutFamily hc Ξ hNames F G) F
    (fun x => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
      ((selectedSumLeftCutRowIso hc Ξ hNames F G x).symm hc _))
  have hR := selected_family_field_integral_independent hc C Ξ hΞ FBase hNames γ hγ hγ1
    (selectedSumRightCutFamily hc Ξ hNames F G) G
    (fun x => VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
      ((selectedSumRightCutRowIso hc Ξ hNames F G x).symm hc _))
  exact (selected_family_field_integral_label_partition hc C Ξ hΞ FBase hNames γ hγ hγ1
    (selectedVolumeFamilySum F G) (selectedSumTagIndex a b k) (selectedSumLeftTagPredicate hc C)
    (selected_sum_left_tag_gamma hc C Ξ) (selected_sum_right_tag_gamma hc C Ξ)).trans
    (congrArg₂ (fun x y => x+y) hL hR)
end IntegrationInACVF.Section7
