module

public import Integration7.SupportedVolumePermutations
public import Integration7.NormalizedVolumePermutationOperators
public import Integration7.NormalizedVolumeSupports

@[expose] public section

/-! Coordinate permutations give genuine linear maps between normalized
supported function modules and their actual coordinate images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
def normalizedSupportedPermuteBase
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C (pureVFCoordinateImage X σ) :=
  (normalizedVolumeRestriction hc C (pureVFCoordinateImage X σ)).comp
    ((normalizedVolumePermuteBase hc C n σ).comp
      (normalizedSupportedVolumeForget hc C X))

theorem normalized_supported_permute_base_positive
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) (k : ℕ)
    (f : SupportedAERVVolumeFunction hc C X k) :
    normalizedSupportedPermuteBase hc C X σ
      (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f)) =
    normalizedSupportedVolumeGenerator hc C (pureVFCoordinateImage X σ)
      (DirectSum.of (SupportedAERVVolumeFunction hc C (pureVFCoordinateImage X σ)) k
        (supportedVolumePermuteBase hc C X σ f)) := by
  change normalizedVolumeRestriction hc C (pureVFCoordinateImage X σ)
    (normalizedVolumePermuteBase hc C n σ
      (normalizedSupportedVolumeForget hc C X
        (normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) k f)))) = _
  rw [normalized_supported_volume_forget_generator,normalized_volume_permute_base_positive,
    ← supported_volume_permute_base_forget hc C X σ f,
    normalized_volume_restriction_positive,ae_volume_restriction_forget_supported]

theorem normalized_supported_permute_base_forget
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1))) :
    (normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X σ)).comp
      (normalizedSupportedPermuteBase hc C X σ) =
    (normalizedVolumePermuteBase hc C n σ).comp
      (normalizedSupportedVolumeForget hc C X) := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro g
  change normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X σ)
    (normalizedSupportedPermuteBase hc C X σ
      (normalizedSupportedVolumeGenerator hc C X g)) =
    normalizedVolumePermuteBase hc C n σ
      (normalizedSupportedVolumeForget hc C X (normalizedSupportedVolumeGenerator hc C X g))
  induction g using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of k f =>
    rw [normalized_supported_permute_base_positive,normalized_supported_volume_forget_generator,
      normalized_supported_volume_forget_generator,normalized_volume_permute_base_positive,
      supported_volume_permute_base_forget]
theorem normalized_volume_permute_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1)))
    (f : NormalizedVolumeFunction hc C n) (hf : HasNormalizedVolumeSupport hc C X f) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X σ) (normalizedVolumePermuteBase hc C n σ f) := by
  obtain ⟨g,rfl⟩ := hf
  exact ⟨normalizedSupportedPermuteBase hc C X σ g,
    LinearMap.congr_fun (normalized_supported_permute_base_forget hc C X σ) g⟩
end IntegrationInACVF.Section7
