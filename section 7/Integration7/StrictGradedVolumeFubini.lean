module

public import Integration7.GradedIntegralDensityCorrection

@[expose] public section

/-! A coordinate projection discarding at least one VF coordinate sends
every raw function component, including ordinary degree zero, to positive
degree. This permits the genuine determinant correction on its output
and proves raw Fubini without changing the ordinary coefficient category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem positive_graded_inclusion_part_of (n j : ℕ) (hj : 0<j)
    (f : AEVolumeFunctionComponent hc C n j) :
    positiveGradedAEVolumeInclusion hc C n
      (positiveGradedAEVolumePart hc C n (DirectSum.of (AEVolumeFunctionComponent hc C n) j f)) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) j f := by
  cases j with
  | zero => omega
  | succ k => rw [positive_graded_ae_volume_part_of,positive_graded_ae_volume_inclusion_of]

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def strictGradedAEVolumeCoordinateAddHom (E : VFCoordinateProjection (n+1) (p+1)) :
    GradedAEVolumeFunction hc C n →+ PositiveGradedAEVolumeFunction hc C p :=
  (positiveGradedAEVolumePart hc C p).comp
    (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).toAddMonoidHom

theorem strict_graded_coordinate_inclusion (E : VFCoordinateProjection (n+1) (p+1))
    (hE : 0<E.discarded) (f : GradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeInclusion hc C p
      (strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    change positiveGradedAEVolumeInclusion hc C p
      (positiveGradedAEVolumePart hc C p
        (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E (DirectSum.of _ j f))) = _
    rw [graded_ae_volume_coordinate_pushforward_of]
    exact positive_graded_inclusion_part_of hc C p _ (by rw [append_volume_degree_eq]; omega) _

def strictGradedAEVolumeCoordinateLinearMap (E : VFCoordinateProjection (n+1) (p+1)) (hE : 0<E.discarded) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      PositiveGradedAEVolumeFunction hc C p where
  toAddHom := strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
  map_smul' r f := by
    apply positive_graded_ae_volume_inclusion_injective hc C p
    change positiveGradedAEVolumeInclusion hc C p
      (strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E (r • f)) =
      positiveGradedAEVolumeInclusion hc C p
        (r • strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)
    rw [strict_graded_coordinate_inclusion hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE,
      map_smul,map_smul,strict_graded_coordinate_inclusion hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE]

def strictGradedAEVolumeSignedCoordinatePushforward (E : VFCoordinateProjection (n+1) (p+1))
    (hE : 0<E.discarded) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      PositiveGradedAEVolumeFunction hc C p :=
  (positiveGradedAEVolumeDensityRescale hc C (rvPermutationSign (volumeProjectionFibreOrder E))⁻¹
    (rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
    (inv_ne_zero (rvPermutationSign_ne_zero _)) p).comp
      (strictGradedAEVolumeCoordinateLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE)

theorem graded_ae_volume_integral_base_equiv {a b : ℕ} (h : a=b) (f : GradedAEVolumeFunction hc C b) :
    gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a
      (gradedAEVolumeBaseEquiv hc C h f) =
      gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 b f := by
  cases h
  rfl

theorem strict_graded_signed_coordinate_integral_eq_total
    (E : VFCoordinateProjection (n+1) (p+1)) (hE : 0<E.discarded) (f : GradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (strictGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f) =
      gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  let σ := volumeProjectionFibreOrder E
  let c := (rvPermutationSign (M := M) σ)⁻¹
  have hcS : c.val ∈ C.base := rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)
  have hc0 : c ≠ 0 := inv_ne_zero (rvPermutationSign_ne_zero σ)
  have hI : positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
      gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
        (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) :=
    congrArg (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p)
      (strict_graded_coordinate_inclusion hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f)
  calc
    _ = gradedVolumeDensityCorrection hc C c hcS hc0
        (positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
          (strictGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)) :=
      positive_graded_integral_density_correction hc C c hcS hc0 Ξ hΞ hGenerated hNames γ hγ hγ1 p _
    _ = gradedVolumeDensityCorrection hc C c hcS hc0
        (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
          (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)) := congrArg _ hI
    _ = gradedVolumeDensityCorrection hc C c hcS hc0
        (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (p+E.discarded)
          (gradedAEVolumePermutationLinearMap hc C (p+E.discarded) σ
            (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E) f))) :=
      congrArg _ (graded_ae_volume_coordinate_ordered_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)
    _ = gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (p+E.discarded)
          (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E) f) :=
      graded_ae_volume_integral_signed_permutation hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ σ _
    _ = _ := graded_ae_volume_integral_base_equiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ f

theorem strict_graded_volume_fubini
    (E : VFCoordinateProjection (n+1) (p+1)) (D : VFCoordinateProjection (n+1) (q+1))
    (hE : 0<E.discarded) (hD : 0<D.discarded) (f : GradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (strictGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f) =
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 q
      (strictGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D hD f) :=
  (strict_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f).trans
    (strict_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D hD f).symm
end IntegrationInACVF.Section7
