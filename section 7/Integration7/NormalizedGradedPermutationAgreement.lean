import Integration7.GradedVolumeCoordinatePushforwards
import Integration7.NormalizedOrdinaryHeadAgreement
import Integration7.NormalizedVolumeCoordinateOperators

/-! Normalization of the actual full raw coordinate operators agrees
with the independently constructed normalized linear operators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_volume_permute_base_ordinary (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    normalizedVolumePermuteBase hc C n σ
      (normalizedVolumeFunctionGenerator hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 f)) =
    normalizedVolumeFunctionGenerator hc C n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 (aeOrdinaryRVVolumeFunctionPermuteBase hc C σ f)) := by
  rw [normalized_ordinary_function_positive_generator,normalized_volume_permute_base_positive,
    ae_ordinary_permute_base_positive_coefficient]
  exact (normalized_ordinary_function_positive_generator hc C n _).symm

theorem normalized_volume_permute_base_generator (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumePermuteBase hc C n σ (normalizedVolumeFunctionGenerator hc C n f) =
      normalizedVolumeFunctionGenerator hc C n (gradedAEVolumePermutationLinearMap hc C n σ f) := by
  induction f using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero,map_zero,map_zero]
  | add f g hf hg => rw [map_add,map_add,hf,hg,map_add,map_add]
  | of j f =>
    rw [graded_ae_volume_permutation_of]
    cases j with
    | zero => exact normalized_volume_permute_base_ordinary hc C n σ f
    | succ k => exact normalized_volume_permute_base_positive hc C n k σ f

theorem normalized_volume_base_equiv_generator {a b : ℕ} (h : a=b)
    (f : GradedAEVolumeFunction hc C b) :
    normalizedVolumeBaseDegreeEquiv hc C h (normalizedVolumeFunctionGenerator hc C b f) =
      normalizedVolumeFunctionGenerator hc C a (gradedAEVolumeBaseEquiv hc C h f) := by
  cases h
  rfl

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem normalized_volume_coordinate_pushforward_generator {n p : ℕ}
    (E : VFCoordinateProjection (n+1) (p+1)) (f : GradedAEVolumeFunction hc C n) :
    normalizedVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (normalizedVolumeFunctionGenerator hc C n f) =
    normalizedVolumeFunctionGenerator hc C p
      (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  change normalizedVolumePrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p
    (normalizedVolumePermuteBase hc C (p+E.discarded) (volumeProjectionFibreOrder E)
      (normalizedVolumeBaseDegreeEquiv hc C (volume_projection_index_eq E)
        (normalizedVolumeFunctionGenerator hc C _ f))) = _
  rw [normalized_volume_base_equiv_generator,normalized_volume_permute_base_generator,
    normalized_volume_prefix_integral_generator]
  change _ = normalizedVolumeFunctionGenerator hc C p
    (gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p _)
  rw [graded_ae_volume_prefix_linear_value]
  rfl
end IntegrationInACVF.Section7
