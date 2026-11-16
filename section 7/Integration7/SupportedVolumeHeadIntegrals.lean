module

public import Integration7.SelectedHeadIntegralSupports
public import Integration7.SupportedVolumeFunctionJacobians
public import Integration7.AERVVolumeHeadIntegrals

@[expose] public section

/-! The actual head integral descends to supported AE families. Its
forgetful image is the pre-existing geometric head integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def supportedVolumeHeadIntegral
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M)) :
    SupportedAERVVolumeFunction hc C X k →
      SupportedAERVVolumeFunction hc C (pureVFCoordinateImage X Fin.succ) (k+1) :=
  Quotient.map (fun F =>
    let T := selectedFamilyHeadPreparation hc Ξ hGenerated F.2.val
    ⟨1+T.arity,⟨F.2.val.headIntegral hc Ξ T,
      F.2.val.headIntegral_support hc Ξ T X F.2.property⟩⟩) (by
    intro F G h
    exact selected_family_head_integral_ae_comparison hc Ξ hΞ hNames γ hγ hγ1 F.2.val G.2.val h
      (selectedFamilyHeadPreparation hc Ξ hGenerated F.2.val)
      (selectedFamilyHeadPreparation hc Ξ hGenerated G.2.val))

theorem supported_volume_head_integral_forget
    (X : DefSet (rawVFSpace (M := M) ((n+1)+1)) (C.base : Set M))
    (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C (pureVFCoordinateImage X Fin.succ)
      (supportedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f) =
    aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (supportedVolumeFunctionForget hc C X f) := by
  induction f using Quotient.inductionOn with
  | h F => rfl
end IntegrationInACVF.Section7
