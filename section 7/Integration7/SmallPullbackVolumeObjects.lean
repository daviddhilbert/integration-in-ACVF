import Integration7.RawPullbackVolumeLifts
import Integration7.VolumeLiftFullDimension

/-! A VF-small actual pullback has no essential volume labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (carrier IsRVPullback pullbackObject rvObjectVolume)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem pullback_volume_essential_empty_of_small_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hAP : IsRVPullback (carrier A))
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (hsmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) < n+1) :
    (pullbackCoordinateVolumeObject hc A hAF δ hδ).essential.obj.domain.carrier = ∅ := by
  apply essential_empty_of_volume_lift_small_dimension hc C
  have he := vfDim_eq_of_bijective (rawRVSpace (M := M) 1) (rawPullbackVolumeLiftMap hc A hAP)
    (rawPullbackVolumeLiftMap_bijective hc A hAP)
  exact he ▸ hsmall

end IntegrationInACVF.Section7
