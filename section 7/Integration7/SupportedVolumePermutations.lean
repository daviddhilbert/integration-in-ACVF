module

public import Integration7.PureVFCoordinateImages
public import Integration7.SupportedVolumeFunctionJacobians
public import Integration7.AERVVolumePermutedFunctions

@[expose] public section

/-! Coordinate permutations retain the exact image of the support
on the actual AE family quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def SupportedVolumeFunctionPresentation.permuteBase
    {X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (F : SupportedVolumeFunctionPresentation C X k) (σ : Equiv.Perm (Fin (n+1))) :
    SupportedVolumeFunctionPresentation C (pureVFCoordinateImage X σ) k := by
  refine ⟨F.1,⟨F.2.val.permuteBase σ,?_⟩⟩
  intro p
  have hp := (mem_mixed_vf_permutation_domain F.2.val.domain σ p.val.1 p.val.2).mp p.property
  apply (mem_pure_vf_coordinate_image X σ p.val.1).mpr
  refine ⟨p.val.1 ∘ σ.symm,F.2.property ⟨_,hp⟩,?_⟩
  funext i
  exact congrArg p.val.1 (σ.symm_apply_apply i)

def supportedVolumePermuteBase
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) :
    SupportedAERVVolumeFunction hc C X k → SupportedAERVVolumeFunction hc C (pureVFCoordinateImage X σ) k :=
  Quotient.map (fun F => SupportedVolumeFunctionPresentation.permuteBase C F σ)
    (fun F G h => ae_volume_family_permute_base hc C F.2.val G.2.val σ h)

theorem supported_volume_permute_base_forget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1)))
    (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionForget hc C (pureVFCoordinateImage X σ) (supportedVolumePermuteBase hc C X σ f) =
      aeRVVolumeFunctionPermuteBase hc C σ (supportedVolumeFunctionForget hc C X f) := by
  induction f using Quotient.inductionOn with
  | h F => rfl
end IntegrationInACVF.Section7
