import Integration7.CanonicalVolumeFamilyIntegrals
import IntegrationSection5.NaturalContractionGamma

/-! The contraction producer requires an actual VF field base.
VF/Gamma generation is not needed for this choice or the checked
same-order integral comparison. This permits genuine frozen contexts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

def selectedFamilyFieldIntegralContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (σ : Equiv.Perm (Fin n)) :
    StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.densityGraph.domain
  exact Classical.choose (standard_contraction_exists_with_natural_graph C.saturated C.model00 B C.small
    FBase (Set.Subset.refl _) A ((gammaLogicInput B).real_set _ (setDefinable A)) σ)

def selectedFamilyFieldCanonicalIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) : PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  positiveVolumeBlowupClass hc C
    (F.canonicalIntegralObject hc Ξ (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)))

theorem selected_family_field_integral_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F = selectedFamilyFieldCanonicalIntegral hc C Ξ FBase G :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_canonical_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F G hCommon
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _))
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase G (Equiv.refl _)))

theorem selected_family_field_integral_eq_canonical
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (FBase : VFFieldBase (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F = selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_canonical_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F F
      (fun x => VolumeBlowupEquivalent.refl hc (vfParameterVolumeContext C x) (F.rowInContext x))
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _))
      (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)))

def selectedFamilyFieldAppendedIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) : PositiveVolumeBlowupClasses hc C (appendVolumeDegree (n+1) k) :=
  positiveVolumeBlowupClass hc C
    (F.standardAppendObject hc Ξ (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)))

theorem selected_family_field_appended_integral_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) (Equiv.refl _)) :
    selectedFamilyFieldAppendedIntegral hc C Ξ FBase F =
      positiveVolumeBlowupClass hc C (F.standardAppendObject hc Ξ T) :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F F
      (fun x => VolumeBlowupEquivalent.refl hc (vfParameterVolumeContext C x) (F.rowInContext x))
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)) T)

end IntegrationInACVF.Section7
