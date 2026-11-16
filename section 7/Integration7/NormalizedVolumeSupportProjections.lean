module

public import Integration7.NormalizedVolumeSupports

@[expose] public section

/-! The actual support projection is idempotent and has exactly the
proved supported-function submodule as its image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedVolumeSupportProjection
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] NormalizedVolumeFunction hc C n :=
  (normalizedSupportedVolumeForget hc C X).comp (normalizedVolumeRestriction hc C X)

theorem normalized_volume_support_projection_idempotent
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedVolumeFunction hc C n) :
    normalizedVolumeSupportProjection hc C X (normalizedVolumeSupportProjection hc C X f) =
      normalizedVolumeSupportProjection hc C X f := by
  change normalizedSupportedVolumeForget hc C X (normalizedVolumeRestriction hc C X
    (normalizedSupportedVolumeForget hc C X (normalizedVolumeRestriction hc C X f))) = _
  rw [show normalizedVolumeRestriction hc C X
    (normalizedSupportedVolumeForget hc C X (normalizedVolumeRestriction hc C X f)) =
      normalizedVolumeRestriction hc C X f from
        congrArg (fun I => I (normalizedVolumeRestriction hc C X f)) (normalized_volume_restriction_forget hc C X)]
  rfl

theorem normalized_volume_support_projection_mem
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedVolumeFunction hc C n) :
    HasNormalizedVolumeSupport hc C X (normalizedVolumeSupportProjection hc C X f) :=
  normalized_supported_volume_has_support hc C X _

theorem normalized_volume_support_projection_fixed_iff
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedVolumeFunction hc C n) :
    normalizedVolumeSupportProjection hc C X f=f ↔ HasNormalizedVolumeSupport hc C X f :=
  (normalized_volume_support_iff_projection hc C X f).symm

theorem normalized_volume_support_projection_range
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    (normalizedVolumeSupportProjection hc C X).range = normalizedVolumeSupportSubmodule hc C X := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact normalized_volume_support_projection_mem hc C X g
  · intro h
    exact ⟨f,(normalized_volume_support_projection_fixed_iff hc C X f).mpr h⟩
end IntegrationInACVF.Section7
