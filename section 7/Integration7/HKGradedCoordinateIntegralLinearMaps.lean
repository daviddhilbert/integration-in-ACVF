import Integration7.HKGlobalJacobianLinearMaps
import Integration7.HKGradedPrefixIntegralLinearMaps
import Integration7.HKGradedVolumeCoordinateFubini

/-! Raw arbitrary-coordinate integration is linear over every corrected
coefficient degree. Its underlying map is the actual signed geometric
coordinate integral already proved to satisfy Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def gradedAEVolumeBaseLinearEquiv {a b : ℕ} (h : a=b) :
    GradedAEVolumeFunction hc C b ≃ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C a := by
  cases h
  exact LinearEquiv.refl _ _

theorem graded_ae_volume_base_linear_value {a b : ℕ} (h : a=b)
    (f : GradedAEVolumeFunction hc C b) :
    gradedAEVolumeBaseLinearEquiv hc C h f = gradedAEVolumeBaseEquiv hc C h f := by
  cases h
  rfl

def gradedAEVolumeCoordinatePermutationLinearMap (σ : Equiv.Perm (Fin (n+1))) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n :=
  gradedAEVolumeJacobianLinearMap hc C _ (pure_vf_univ_permutation_bijective C σ)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def gradedAEVolumeCoordinateIntegralLinearMap (E : VFCoordinateProjection (n+1) (p+1)) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C p :=
  (gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p).comp
    ((gradedAEVolumeCoordinatePermutationLinearMap hc C (volumeProjectionFibreOrder E)).comp
      (gradedAEVolumeBaseLinearEquiv hc C (volume_projection_index_eq E)).toLinearMap)

theorem graded_ae_volume_coordinate_linear_value (E : VFCoordinateProjection (n+1) (p+1))
    (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f =
      gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f := by
  change gradedAEVolumePrefixIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p
    (gradedAEVolumeCoordinatePermutationLinearMap hc C (volumeProjectionFibreOrder E)
      (gradedAEVolumeBaseLinearEquiv hc C (volume_projection_index_eq E) f)) = _
  rw [graded_ae_volume_prefix_linear_value,graded_ae_volume_base_linear_value]
  rfl

end IntegrationInACVF.Section7.HK
