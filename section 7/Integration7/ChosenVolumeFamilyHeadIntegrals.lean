module

public import Integration7.VolumeFamilyHeadIntegralComparison
public import IntegrationSection5.GammaHeadPreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A genuine generated-base head preparation supplies a chosen
representative of the head fibre integral. Its quotient value is
independent of that choice and of pointwise representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def selectedFamilyHeadPreparation
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) :
    HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.densityGraph.domain
  exact Classical.choose (gamma_head_preparation C.saturated C.model00 B C.small
    (generatedBaseVFField hGenerated) (Set.Subset.refl _) A
    ((gammaLogicInput B).real_set _ (setDefinable A)))

def selectedFamilyHeadIntegralRepresentative
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C (n+1) a k) : SelectedVolumeFunctionPresentation C n (k+1) :=
  let T := selectedFamilyHeadPreparation hc Ξ hGenerated F
  ⟨1+T.arity,F.headIntegral hc Ξ T⟩

def pointwiseRVVolumeFunctionHeadIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    PointwiseRVVolumeFunction hc C (n+1) k → PointwiseRVVolumeFunction hc C n (k+1) :=
  Quotient.lift (fun F => Quotient.mk _ (selectedFamilyHeadIntegralRepresentative hc Ξ hGenerated F.2)) (by
    intro F G h
    apply Quotient.sound
    intro x
    exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mpr
      (selected_family_head_integral_comparison hc Ξ hΞ hNames γ hγ hγ1 F.2 G.2
        (fun y => (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C y)).mp (h y))
        (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)
        (selectedFamilyHeadPreparation hc Ξ hGenerated G.2) x))

theorem pointwise_rv_volume_function_head_integral_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) (x : Fin n → VF (M := M)) :
    pointwiseRVVolumeFunctionValue hc C
      (pointwiseRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ ⟨a,F⟩)) x =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) :=
  selected_family_head_integral_choice_independent hc Ξ hΞ hNames γ hγ hγ1 F
    (selectedFamilyHeadPreparation hc Ξ hGenerated F) T x

end IntegrationInACVF.Section7
