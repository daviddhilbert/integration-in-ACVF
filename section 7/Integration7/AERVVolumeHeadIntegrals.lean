import Integration7.AERVVolumeHeadIntegralComparison

/-! Integration of one VF head on the actual almost-everywhere
function quotient. Its representative formula holds for every head
preparation and agrees with the pointwise quotient construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def aeRVVolumeFunctionHeadIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) :
    AERVVolumeFunction hc C (n+1) k → AERVVolumeFunction hc C n (k+1) :=
  Quotient.lift (fun F => Quotient.mk _ (selectedFamilyHeadIntegralRepresentative hc Ξ hGenerated F.2)) (by
    intro F G h
    apply Quotient.sound
    exact selected_family_head_integral_ae_comparison hc Ξ hΞ hNames γ hγ hγ1 F.2 G.2 h
      (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)
      (selectedFamilyHeadPreparation hc Ξ hGenerated G.2))

theorem ae_rv_volume_function_head_integral_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C ((n+1)+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (Quotient.mk _ ⟨a,F⟩) =
      Quotient.mk _ ⟨1+T.arity,F.headIntegral hc Ξ T⟩ := by
  apply Quotient.sound
  exact selected_family_head_integral_ae_comparison hc Ξ hΞ hNames γ hγ hγ1 F F
    (ae_rv_volume_function_equivalent_of_pointwise hc C (fun _ => rfl))
    (selectedFamilyHeadPreparation hc Ξ hGenerated F) T

theorem ae_rv_volume_head_integral_of_pointwise
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : PointwiseRVVolumeFunction hc C ((n+1)+1) k) :
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pointwiseToAERVVolumeFunction hc C f) =
      pointwiseToAERVVolumeFunction hc C
        (pointwiseRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F => rfl

end IntegrationInACVF.Section7
