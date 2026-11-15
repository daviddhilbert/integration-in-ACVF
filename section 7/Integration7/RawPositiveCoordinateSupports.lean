import Integration7.SupportedVolumePermutations
import Integration7.SupportedVolumeHeadIntegrals
import Integration7.NormalizedCoordinateImageGeometry
import Integration7.SignedPositiveCoordinatePushforwards

/-! Actual supported AE representatives survive raw coordinate
integration and determinant rescaling. The target support is the literal
image of the original definable VF domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

abbrev HasRawPositiveVolumeSupport
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (f : AERVVolumeFunction hc C n k) : Prop :=
  ∃ g : SupportedAERVVolumeFunction hc C X k, supportedVolumeFunctionForget hc C X g=f

theorem raw_positive_rescale_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (f : AERVVolumeFunction hc C n k) (hf : HasRawPositiveVolumeSupport hc C X f)
    (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c≠0) :
    HasRawPositiveVolumeSupport hc C X (aeRVVolumeFunctionRescale hc C c hcS hc0 f) := by
  obtain ⟨g,rfl⟩ := hf
  induction g using Quotient.inductionOn with
  | h F =>
    exact ⟨Quotient.mk _ ⟨F.1,⟨F.2.val.rescale c hcS hc0,F.2.property⟩⟩,rfl⟩

theorem raw_positive_base_reindex_preserves_support {a b : ℕ} (h : a=b)
    (X : DefSet (rawVFSpace (M := M) (b+1)) (C.base : Set M))
    (f : AERVVolumeFunction hc C b k) (hf : HasRawPositiveVolumeSupport hc C X f) :
    HasRawPositiveVolumeSupport hc C (pureVFCoordinateImage X (finCongr (congrArg Nat.succ h)))
      (aeRVVolumeFunctionReindexBase hc C h f) := by
  cases h
  change HasRawPositiveVolumeSupport hc C (pureVFCoordinateImage X id) f
  rw [pure_vf_coordinate_image_id]
  exact hf

theorem raw_positive_permutation_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (σ : Equiv.Perm (Fin (n+1)))
    (f : AERVVolumeFunction hc C n k) (hf : HasRawPositiveVolumeSupport hc C X f) :
    HasRawPositiveVolumeSupport hc C (pureVFCoordinateImage X σ) (aeRVVolumeFunctionPermuteBase hc C σ f) := by
  obtain ⟨g,rfl⟩ := hf
  exact ⟨supportedVolumePermuteBase hc C X σ g,supported_volume_permute_base_forget hc C X σ g⟩

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem raw_positive_prefix_preserves_support : ∀ (r n k : ℕ)
    (X : DefSet (rawVFSpace (M := M) ((n+r)+1)) (C.base : Set M))
    (f : AERVVolumeFunction hc C (n+r) k), HasRawPositiveVolumeSupport hc C X f →
    HasRawPositiveVolumeSupport hc C (pureVFPrefixImage r n X)
      (aeRVVolumeFunctionPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 r n k f) := by
  intro r
  induction r with
  | zero => intro n k X f hf; exact hf
  | succ r ih =>
    intro n k X f hf
    obtain ⟨g,rfl⟩ := hf
    apply ih n (k+1) (pureVFCoordinateImage X Fin.succ)
    exact ⟨supportedVolumeHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g,
      supported_volume_head_integral_forget hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X g⟩

theorem raw_positive_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) (hf : HasRawPositiveVolumeSupport hc C X f) :
    HasRawPositiveVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex)
      (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  have hCast := raw_positive_base_reindex_preserves_support hc C (volume_projection_index_eq E) X f hf
  have hPerm := raw_positive_permutation_preserves_support hc C _ (volumeProjectionFibreOrder E) _ hCast
  have hPrefix := raw_positive_prefix_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p k _ _ hPerm
  rw [volume_projection_iterated_image] at hPrefix
  exact hPrefix

theorem raw_positive_signed_coordinate_preserves_support
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)) (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) (hf : HasRawPositiveVolumeSupport hc C X f) :
    HasRawPositiveVolumeSupport hc C (pureVFCoordinateImage X E.retainedIndex)
      (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) :=
  raw_positive_rescale_preserves_support hc C _ _
    (raw_positive_coordinate_preserves_support hc C Ξ hΞ hGenerated hNames γ hγ hγ1 X E f hf) _ _ _
end IntegrationInACVF.Section7
