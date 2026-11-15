import Integration7.CoordinateVolumeIntegralNormalizers

/-! Positive homogeneous coordinate Fubini with every RV coordinate
identification explicit. The iterated total is computed by the actual
coordinate pushforward, then returned to the original global coordinate
order by the previously specified coordinate-only normalizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q k : ℕ}

def normalizedCoordinateVolumeIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (E : VFCoordinateProjection (n+1) (p+1)) (f : AERVVolumeFunction hc C n k) :
    PositiveVolumeBlowupClasses hc C ((k+1)+n) :=
  coordinateVolumeIntegralNormalizer hc C E k
    (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))

theorem normalized_coordinate_volume_integral_eq_total
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (E : VFCoordinateProjection (n+1) (p+1)) (f : AERVVolumeFunction hc C n k) :
    normalizedCoordinateVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f =
      aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  let g := aeRVVolumeFunctionReindexBase hc C (volume_projection_index_eq E) f
  let σ := volumeProjectionFibreOrder E
  let hDegree := congrArg (fun j => (k+1)+j) (volume_projection_index_eq E).symm
  have hPrefix := ae_rv_volume_coordinate_pushforward_ordered_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f
  have hCast : positiveVolumeClassReindexDegree hc C (append_volume_degree_split p E.discarded k)
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f)) =
      aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (aeRVVolumeFunctionPermuteBase hc C σ g) :=
    eq_of_heq ((positive_volume_class_reindex_degree_heq hc C (append_volume_degree_split p E.discarded k) _).trans hPrefix)
  unfold normalizedCoordinateVolumeIntegral coordinateVolumeIntegralNormalizer
  rw [hCast,ae_rv_volume_integral_from_appended hc C Ξ hΞ hGenerated hNames γ hγ hγ1,
    ae_rv_volume_function_integral_restore_order hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact eq_of_heq ((positive_volume_class_reindex_degree_heq hc C hDegree _).trans
    (ae_rv_volume_integral_reindex_base_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (volume_projection_index_eq E) f))

theorem positive_coordinate_volume_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (E : VFCoordinateProjection (n+1) (p+1)) (D : VFCoordinateProjection (n+1) (q+1))
    (f : AERVVolumeFunction hc C n k) :
    normalizedCoordinateVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f =
      normalizedCoordinateVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f :=
  (normalized_coordinate_volume_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f).trans
    (normalized_coordinate_volume_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f).symm

end IntegrationInACVF.Section7
