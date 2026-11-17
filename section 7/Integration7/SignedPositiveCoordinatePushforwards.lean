module

public import Integration7.AppendedIntegralDensityRescaling
public import Integration7.CoordinateVolumeIntegralNormalizers

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Coordinate pushforward with the actual determinant-density factor
of its VF split. The correction acts on the resulting family itself.
Its raw iterated total is the original total before normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def aeRVVolumeSignedCoordinatePushforward (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) : AERVVolumeFunction hc C p (appendVolumeDegree E.discarded k) :=
  aeRVVolumeFunctionRescale hc C (rvPermutationSign (volumeProjectionFibreOrder E))⁻¹
    (rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
    (inv_ne_zero (rvPermutationSign_ne_zero _))
    (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)

theorem ae_rv_volume_appended_integral_reindex_base_heq {u v j : ℕ} (h : u=v)
    (f : AERVVolumeFunction hc C v j) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeFunctionReindexBase hc C h f))
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  cases h
  rfl

theorem positive_signed_coordinate_integral_eq_total (E : VFCoordinateProjection (n+1) (p+1))
    (f : AERVVolumeFunction hc C n k) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  let σ := volumeProjectionFibreOrder E
  let g := aeRVVolumeFunctionReindexBase hc C (volume_projection_index_eq E) f
  let c := (rvPermutationSign (M := M) σ)⁻¹
  have hcS : c.val ∈ C.base := rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)
  have hc0 : c ≠ 0 := inv_ne_zero (rvPermutationSign_ne_zero σ)
  have hRescale := ae_rv_volume_appended_integral_density_rescale hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) c hcS hc0
  have hOrdered := ae_rv_volume_coordinate_pushforward_ordered_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f
  have hScale := dependent_degree_map_heq
    (fun j => positiveVolumeClassRescaleDefinable (k := j) hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0)
    (append_volume_degree_split p E.discarded k).symm hOrdered
  have hSign := ae_rv_volume_appended_integral_signed_permutation hc C Ξ hΞ hGenerated hNames γ hγ hγ1 g σ
  have hBase := ae_rv_volume_appended_integral_reindex_base_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (volume_projection_index_eq E) f
  exact (heq_of_eq hRescale).trans (hScale.trans ((heq_of_eq hSign).trans hBase))

theorem positive_signed_coordinate_volume_fubini
    (E : VFCoordinateProjection (n+1) (p+1)) (D : VFCoordinateProjection (n+1) (q+1))
    (f : AERVVolumeFunction hc C n k) :
    HEq (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f)) :=
  (positive_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f).trans
    (positive_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f).symm
end IntegrationInACVF.Section7
