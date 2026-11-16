module

public import Integration7.PositiveGradedVolumeIntegration
public import Integration7.GradedVolumeCoordinatePushforwards
public import Integration7.SignedPositiveCoordinatePushforwards

@[expose] public section

/-! The actual signed coordinate pushforward on finite positive graded
functions is linear over every raw coefficient degree. Its determinant
correction acts on the intermediate AE families themselves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem graded_ae_volume_coordinate_pushforward_positive_of
    (E : VFCoordinateProjection (n+1) (p+1)) (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1) f) =
    DirectSum.of (AEVolumeFunctionComponent hc C p) (appendVolumeDegree E.discarded j+1)
      (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  rw [graded_ae_volume_coordinate_pushforward_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply Sigma.ext (show appendVolumeDegree E.discarded (j+1)=appendVolumeDegree E.discarded j+1 by
    simp only [append_volume_degree_eq]; omega)
  have hBase : aeVolumeFunctionComponentBaseEquiv hc C (volume_projection_index_eq E) (j+1) f =
      aeRVVolumeFunctionReindexBase hc C (volume_projection_index_eq E) f := by
    have aux : ∀ {a b : ℕ} (h : a=b) (g : AERVVolumeFunction hc C b j),
        aeVolumeFunctionComponentBaseEquiv hc C h (j+1) g = aeRVVolumeFunctionReindexBase hc C h g := by
      intro a b h g
      cases h
      rfl
    exact aux _ f
  change HEq (aeVolumeFunctionComponentPrefixIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    E.discarded p (j+1)
      (aeRVVolumeFunctionPermuteBase hc C (volumeProjectionFibreOrder E)
        (aeVolumeFunctionComponentBaseEquiv hc C (volume_projection_index_eq E) (j+1) f))) _
  rw [hBase]
  exact ae_volume_component_prefix_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p j _

def positiveGradedAEVolumeCoordinateAddHom (E : VFCoordinateProjection (n+1) (p+1)) :
    PositiveGradedAEVolumeFunction hc C n →+ PositiveGradedAEVolumeFunction hc C p :=
  (positiveGradedAEVolumePart hc C p).comp
    ((gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E).toAddMonoidHom.comp
      (positiveGradedAEVolumeInclusion hc C n).toAddMonoidHom)

theorem positive_graded_ae_volume_coordinate_of (E : VFCoordinateProjection (n+1) (p+1))
    (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E (DirectSum.of _ j f) =
      DirectSum.of (AERVVolumeFunction hc C p) (appendVolumeDegree E.discarded j)
        (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  change positiveGradedAEVolumePart hc C p
    (gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (positiveGradedAEVolumeInclusion hc C n (DirectSum.of _ j f))) = _
  rw [positive_graded_ae_volume_inclusion_of,graded_ae_volume_coordinate_pushforward_positive_of,
    positive_graded_ae_volume_part_of]

theorem positive_graded_coordinate_inclusion (E : VFCoordinateProjection (n+1) (p+1))
    (f : PositiveGradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeInclusion hc C p
      (positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    gradedAEVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (positiveGradedAEVolumeInclusion hc C n f) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [positive_graded_ae_volume_coordinate_of,positive_graded_ae_volume_inclusion_of,
      positive_graded_ae_volume_inclusion_of,graded_ae_volume_coordinate_pushforward_positive_of]

def positiveGradedAEVolumeCoordinateLinearMap (E : VFCoordinateProjection (n+1) (p+1)) :
    PositiveGradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      PositiveGradedAEVolumeFunction hc C p where
  toAddHom := positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
  map_smul' r f := by
    apply positive_graded_ae_volume_inclusion_injective hc C p
    change positiveGradedAEVolumeInclusion hc C p
      (positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E (r • f)) =
      positiveGradedAEVolumeInclusion hc C p
        (r • positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)
    rw [positive_graded_coordinate_inclusion,map_smul,map_smul,map_smul,positive_graded_coordinate_inclusion]

def positiveGradedAEVolumeSignedCoordinatePushforward (E : VFCoordinateProjection (n+1) (p+1)) :
    PositiveGradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      PositiveGradedAEVolumeFunction hc C p :=
  (positiveGradedAEVolumeDensityRescale hc C (rvPermutationSign (volumeProjectionFibreOrder E))⁻¹
    (rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
    (inv_ne_zero (rvPermutationSign_ne_zero _)) p).comp
      (positiveGradedAEVolumeCoordinateLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E)

theorem positive_graded_signed_coordinate_of (E : VFCoordinateProjection (n+1) (p+1))
    (j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E
      (DirectSum.of _ j f) =
      DirectSum.of (AERVVolumeFunction hc C p) (appendVolumeDegree E.discarded j)
        (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) := by
  change positiveGradedAEVolumeDensityRescale hc C _ _ _ p
    (positiveGradedAEVolumeCoordinateAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E (DirectSum.of _ j f)) = _
  rw [positive_graded_ae_volume_coordinate_of,positive_graded_density_rescale_of]
  rfl
end IntegrationInACVF.Section7
