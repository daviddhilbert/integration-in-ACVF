module

public import Integration7.FieldBaseVolumeIntegralAdditivity
public import Integration7.AppendedVolumeIntegralAddHom

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The fixed, additive coordinate normalization transports field-base
additivity to the actual coefficient-first integral used on head fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_field_integral_from_appended
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    canonicalFromAppendedVolumeAddEquiv hc C n k (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) =
      selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F := by
  have h := positiveVolumeBlowupClass_iso hc C
    (selectedIntegralNormalizationIso hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
      F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)))
  change positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k).symm
    (positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C
      (appendedToOriginalVolumePermutation (n+1) k) (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F)) = _
  rw [show positiveVolumeClassPermute (k := appendVolumeDegree (n+1) k) hc C
      (appendedToOriginalVolumePermutation (n+1) k) (selectedFamilyFieldAppendedIntegral hc C Ξ FBase F) =
      positiveVolumeClassReindexDegree hc C (selected_append_degree_eq n k)
        (selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F) from h]
  exact (positiveVolumeClassDegreeReindexEquiv hc C (selected_append_degree_eq n k)).left_inv
    (selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F)

theorem selected_family_field_appended_integral_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase (selectedVolumeFamilySum F G) =
      selectedFamilyFieldAppendedIntegral hc C Ξ FBase F + selectedFamilyFieldAppendedIntegral hc C Ξ FBase G := by
  apply (canonicalFromAppendedVolumeAddEquiv hc C n k).injective
  rw [map_add,selected_family_field_integral_from_appended,selected_family_field_integral_from_appended,
    selected_family_field_integral_from_appended]
  exact selected_family_field_canonical_integral_add hc C Ξ hΞ FBase hNames γ hγ hγ1 F G
end IntegrationInACVF.Section7
