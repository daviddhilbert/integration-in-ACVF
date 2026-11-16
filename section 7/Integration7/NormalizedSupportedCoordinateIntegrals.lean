module

public import Integration7.NormalizedCoordinateSupportPreservation

@[expose] public section

/-! Coordinate integration on the supported normalized function spaces.
The target is the literal projected support and forgetting support
recovers the unchanged full coordinate operator. -/
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
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def normalizedSupportedCoordinatePushforward (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedSupportedVolumeFunction hc C X →ₗ[NormalizedRVVolumeRing hc C]
      NormalizedSupportedVolumeFunction hc C (pureVFCoordinateImage X E.retainedIndex) :=
  (normalizedVolumeRestriction hc C (pureVFCoordinateImage X E.retainedIndex)).comp
    ((normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).comp
      (normalizedSupportedVolumeForget hc C X))

theorem normalized_supported_coordinate_pushforward_forget (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E : VFCoordinateProjection (n+1) (p+1)) :
    (normalizedSupportedVolumeForget hc C (pureVFCoordinateImage X E.retainedIndex)).comp
      (normalizedSupportedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) =
    (normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).comp
      (normalizedSupportedVolumeForget hc C X) := by
  apply LinearMap.ext
  intro f
  exact (normalized_volume_support_iff_projection hc C _ _).mp
    (normalized_volume_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E
      (normalizedSupportedVolumeForget hc C X f) (normalized_supported_volume_has_support hc C X f))

theorem normalized_supported_coordinate_total_fubini (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (E : VFCoordinateProjection (n+1) (p+1)) :
    (normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (pureVFCoordinateImage X E.retainedIndex)).comp
      (normalizedSupportedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) =
    normalizedSupportedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X := by
  apply LinearMap.ext
  intro f
  exact (congrArg (normalizedVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p)
    (LinearMap.congr_fun (normalized_supported_coordinate_pushforward_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E) f)).trans
    (normalized_volume_coordinate_total_value hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (normalizedSupportedVolumeForget hc C X f))
end IntegrationInACVF.Section7
