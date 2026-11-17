module

public import Integration7.NormalizedCoordinateImageGeometry
public import Integration7.NormalizedSupportedPermutations
public import Integration7.NormalizedPrefixSupportPreservation
public import Integration7.NormalizedVolumeCoordinateOperators

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every nonempty VF coordinate pushforward preserves the actual
image of a supported normalized function, through the literal cast,
permutation and prefix contraction defining the operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_volume_base_degree_preserves_support {a b : ℕ} (h : a=b)
    (X : DefSet (rawVFSpace (M := M) (b+1)) (C.base : Set M))
    (f : NormalizedVolumeFunction hc C b) (hf : HasNormalizedVolumeSupport hc C X f) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X (finCongr (congrArg Nat.succ h)))
      (normalizedVolumeBaseDegreeEquiv hc C h f) := by
  cases h
  have he : finCongr (congrArg Nat.succ (rfl : a=a)) = Equiv.refl (Fin (a+1)) := rfl
  rw [he]
  change HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X id) f
  rw [pure_vf_coordinate_image_id]
  exact hf

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : NormalizedVolumeFunction hc C n) (hf : HasNormalizedVolumeSupport hc C X f) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex)
      (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  have hCast := normalized_volume_base_degree_preserves_support hc C (volume_projection_index_eq E) X f hf
  have hPerm := normalized_volume_permute_preserves_support hc C _ (volumeProjectionFibreOrder E) _ hCast
  have hPrefix := normalized_volume_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    E.discarded p _ _ hPerm
  rw [volume_projection_iterated_image] at hPrefix
  exact hPrefix
end IntegrationInACVF.Section7
