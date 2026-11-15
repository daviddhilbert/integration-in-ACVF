import Integration7.FrozenHeadVolumeIntegrals
import Integration7.HeadFibreIntegralIsomorphisms
import Integration7.ChosenVolumeFamilyHeadIntegrals
import Integration7.PositiveVolumeClassExtensions

/-! Pointwise fibre semantics: the actual head-integral row equals the
actual unary frozen-family integral in its proved definable-closure
context. Old selected coordinates precede the new head coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def selectedFamilyFrozenHeadAppendedIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) :
    PositiveVolumeBlowupClasses hc (frozenHeadVolumeContext hc C x) (k+1) :=
  selectedFamilyFieldAppendedIntegral hc (frozenHeadVolumeContext hc C x) Ξ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x)) (F.frozenHeadFamily hc x)

theorem selected_head_integral_is_frozen_fibre_integral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (x : Fin n → VFType (M := M)) :
    positiveVolumeClassExtend hc (vfParameterVolumeContext C x) (frozenHeadVolumeContext hc C x)
      (frozen_head_volume_context_contains hc C x) (k+1)
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x)) =
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x := by
  let D := frozenHeadVolumeContext hc C x
  let hD := frozen_head_volume_context_contains hc C x
  let R := headFibreStandardContraction hc C D F T x hD
  have he := positiveVolumeBlowupClass_iso hc D (headFibreIntegralVolumeIso hc C D Ξ F T x hD)
  change positiveVolumeBlowupClass hc D (((F.headIntegral hc Ξ T).rowInContext x).extend hD) = _
  exact he.trans (selected_family_field_appended_integral_contraction hc D Ξ hΞ
    (definablyClosedVolumeContextField hc (vfParameterVolumeContext C x))
    (frozen_head_volume_context_common_names hc C Ξ hNames x) γ hγ hγ1
    (F.frozenHeadFamily hc x) R).symm

theorem pointwise_rv_volume_head_integral_fibre_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M)) :
    positiveVolumeClassExtend hc (vfParameterVolumeContext C x) (frozenHeadVolumeContext hc C x)
      (frozen_head_volume_context_contains hc C x) (k+1)
      (pointwiseRVVolumeFunctionValue hc C
        (pointwiseRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
          (Quotient.mk _ ⟨a,F⟩)) x) =
    selectedFamilyFrozenHeadAppendedIntegral hc C Ξ F x := by
  rw [pointwise_rv_volume_function_head_integral_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F
    (selectedFamilyHeadPreparation hc Ξ hGenerated F) x]
  exact selected_head_integral_is_frozen_fibre_integral hc C Ξ hΞ hNames γ hγ hγ1 F _ x

end IntegrationInACVF.Section7
