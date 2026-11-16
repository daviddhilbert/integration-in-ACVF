import Integration7.HKZeroVFCoproductIsomorphisms
import Integration7.HKVolumeCoproductIsomorphisms

/-! Weighted zero lifts preserve the concrete tagged coproduct and the
literal density of either summand. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroLiftCoprodIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    ZeroVFVolumeIso (zeroVFCoprod hc C (zeroLift U) (zeroLift V))
      (zeroLift (coprod (C.base : Set M) 0 U V)) where
  iso := ordinaryZeroLiftCoprodIso hc C U.underlying V.underlying
  density w := by
    let e := ordinaryZeroLiftCoprodIso hc C U.underlying V.underlying
    rcases zero_vf_coprod_cases hc C (zeroLift U) (zeroLift V) w with ⟨u,hu⟩ | ⟨v,hv⟩
    · have hLabel : liftLabelMap (coprod (C.base : Set M) 0 U V).underlying.obj
          (finiteZeroVFMap e (zeroVFCoprodLeftMap hc C (zeroLift U) (zeroLift V) u)) =
          rvCoprodLeftMap U.underlying.obj V.underlying.obj (liftLabelMap U.underlying.obj u) := Subtype.ext rfl
      rw [← hu,zero_vf_coprod_density_left]
      change U.form.value (liftLabelMap U.underlying.obj u) =
        (coprod (C.base : Set M) 0 U V).form.value
          (liftLabelMap (coprod (C.base : Set M) 0 U V).underlying.obj
            (finiteZeroVFMap e (zeroVFCoprodLeftMap hc C (zeroLift U) (zeroLift V) u)))
      rw [hLabel]
      exact (coprod_density_left 0 U V _).symm
    · have hLabel : liftLabelMap (coprod (C.base : Set M) 0 U V).underlying.obj
          (finiteZeroVFMap e (zeroVFCoprodRightMap hc C (zeroLift U) (zeroLift V) v)) =
          rvCoprodRightMap U.underlying.obj V.underlying.obj (liftLabelMap V.underlying.obj v) := Subtype.ext rfl
      rw [← hv,zero_vf_coprod_density_right]
      change V.form.value (liftLabelMap V.underlying.obj v) =
        (coprod (C.base : Set M) 0 U V).form.value
          (liftLabelMap (coprod (C.base : Set M) 0 U V).underlying.obj
            (finiteZeroVFMap e (zeroVFCoprodRightMap hc C (zeroLift U) (zeroLift V) v)))
      rw [hLabel]
      exact (coprod_density_right 0 U V _).symm

end IntegrationInACVF.Section7.HK
