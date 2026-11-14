import Integration7.VolumeLiftBijections
import Integration7.VFVolumeComposition

/-! Passing from essential lifts to the full original lifts discards
only the actual coordinate-zero set of smaller VF dimension. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def vfVolumeCofullRestrictionIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (A : DefSet (rawMixedSpace (M := M) (k + 1) U.arity) (C.base : Set M))
    (hA : VFCofull U.domain A) : VFVolumeIso (U.restrict A hA.subset) U where
  source := A
  target := A
  source_subset := Set.Subset.refl _
  target_subset := hA.subset
  source_complement_small := by
    change vfDim (rawRVSpace (M := M) 1) (A.sdiff A) < k + 1
    have he : A.sdiff A = DefSet.empty _ (C.base : Set M) := by
      apply DefSet.eq_of_carrier_eq
      exact Set.sdiff_self
    rw [he]
    exact (Dimension.dim_empty rawVFSpace
      (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv U.arity)).trans_lt
        (Nat.zero_lt_succ k)
  target_complement_small := hA.small
  bijection := VFVolumeBijection.of_preserving_vf_and_density hc C
    (Map.id A) Function.bijective_id (fun _ => rfl) (fun _ => rfl)

theorem rvVolumeLift_essential_cofull (U : PositiveRVVolumeObject (M := M) S k) :
    VFCofull (rvVolumeLift U).domain (rvVolumeLift U.essentialCore).domain := by
  refine ⟨?_, rvEssentialLift_complement_dim_lt _ U.underlying.obj⟩
  intro p hp
  exact ((mem_rvEssentialLift U.underlying.obj p).mp hp).1

def rvVolumeLiftEssentialIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeIso (rvVolumeLift U.essentialCore) (rvVolumeLift U) :=
  vfVolumeCofullRestrictionIso hc C (rvVolumeLift U)
    (rvVolumeLift U.essentialCore).domain (rvVolumeLift_essential_cofull U)

theorem RVVolumeIso.nonempty_full_lift_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase ⟨(C.base : Set M), Ξ⟩)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    Nonempty (VFVolumeIso (rvVolumeLift U) (rvVolumeLift V)) := by
  obtain ⟨G⟩ := e.nonempty_lift_bijection hc C Ξ hGenerated
  exact ⟨((rvVolumeLiftEssentialIso hc C U).symm hc C).trans hc C
    ((VFVolumeIso.of_bijection G).trans hc C (rvVolumeLiftEssentialIso hc C V))⟩

end IntegrationInACVF.Section7
