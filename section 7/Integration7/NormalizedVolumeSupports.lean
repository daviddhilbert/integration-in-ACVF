import Integration7.NormalizedVolumeBaseRestrictions
import Mathlib.LinearAlgebra.Isomorphisms

/-! Normalized supported functions identify with an actual submodule
of the full function space. Membership is equivalent to being fixed by
the genuine restriction projection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def normalizedVolumeSupportSubmodule
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    Submodule (NormalizedRVVolumeRing hc C) (NormalizedVolumeFunction hc C n) :=
  (normalizedSupportedVolumeForget hc C X).range

abbrev HasNormalizedVolumeSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedVolumeFunction hc C n) : Prop :=
  f ∈ normalizedVolumeSupportSubmodule hc C X

def normalizedSupportedVolumeRangeEquiv
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) :
    NormalizedSupportedVolumeFunction hc C X ≃ₗ[NormalizedRVVolumeRing hc C] normalizedVolumeSupportSubmodule hc C X :=
  LinearEquiv.ofInjective (normalizedSupportedVolumeForget hc C X)
    (normalized_supported_volume_forget_injective hc C X)

theorem normalized_volume_support_iff_projection
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedVolumeFunction hc C n) :
    HasNormalizedVolumeSupport hc C X f ↔
      normalizedSupportedVolumeForget hc C X (normalizedVolumeRestriction hc C X f) = f := by
  constructor
  · rintro ⟨g,rfl⟩
    exact congrArg (normalizedSupportedVolumeForget hc C X)
      (congrArg (fun I => I g) (normalized_volume_restriction_forget hc C X))
  · intro h
    exact ⟨normalizedVolumeRestriction hc C X f,h⟩

theorem normalized_supported_volume_has_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : NormalizedSupportedVolumeFunction hc C X) :
    HasNormalizedVolumeSupport hc C X (normalizedSupportedVolumeForget hc C X f) := ⟨f,rfl⟩

theorem normalized_positive_supported_generator_has_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (j : ℕ)
    (f : SupportedAERVVolumeFunction hc C X j) :
    HasNormalizedVolumeSupport hc C X (normalizedPositiveVolumeFunction hc C n j (supportedVolumeFunctionForget hc C X f)) :=
  ⟨normalizedSupportedVolumeGenerator hc C X (DirectSum.of (SupportedAERVVolumeFunction hc C X) j f),
    normalized_supported_volume_forget_generator hc C X j f⟩
end IntegrationInACVF.Section7
