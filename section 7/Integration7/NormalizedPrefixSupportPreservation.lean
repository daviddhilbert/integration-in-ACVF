import Integration7.NormalizedHeadSupportPreservation
import Integration7.NormalizedVolumePrefixOperators
import Integration7.PureVFPrefixImages

/-! Iterated head integration preserves the actual coordinate image
of every supported normalized input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_prefix_preserves_support : ∀ (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M))
    (f : NormalizedVolumeFunction hc C (n+r)), HasNormalizedVolumeSupport hc C X f →
    HasNormalizedVolumeSupport hc C (pureVFPrefixImage r n X)
      (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) := by
  intro r
  induction r with
  | zero => intro n X f hf; exact hf
  | succ r ih =>
    intro n X f hf
    exact ih n (pureVFCoordinateImage X Fin.succ)
      (normalizedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (n+r) f)
      (normalized_volume_head_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X f hf)

theorem normalized_volume_prefix_coordinate_support (r n : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M))
    (f : NormalizedVolumeFunction hc C (n+r)) (hf : HasNormalizedVolumeSupport hc C X f) :
    HasNormalizedVolumeSupport hc C (pureVFCoordinateImage X (vfPrefixRetainedIndex r n))
      (normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n f) := by
  rw [← pure_vf_prefix_image_eq]
  exact normalized_volume_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n X f hf
end IntegrationInACVF.Section7
