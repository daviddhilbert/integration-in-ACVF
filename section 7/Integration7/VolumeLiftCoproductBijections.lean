module

public import Integration7.VolumeLiftCoproductDomains
public import Integration7.VFVolumeIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The full lift commutes with fixed-degree disjoint unions through
the literal identity map on VF tuples and tagged RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volume_lift_coprod_map_density
    (U V : PositiveRVVolumeObject (M := M) S k)
    (p : ((rvVolumeLift U).coprod (rvVolumeLift V)).domain) :
    ((rvVolumeLift U).coprod (rvVolumeLift V)).form.value p =
      (rvVolumeLift (U.coprod V)).form.value (volumeLiftCoprodMap U V p) := by
  rcases vf_volume_coprod_cases (rvVolumeLift U) (rvVolumeLift V) p with ⟨u,rfl⟩ | ⟨v,rfl⟩
  · rw [vf_volume_coprod_density_left,rvVolumeLift_density]
    exact (coprod_density_left U V (liftLabelMap U.underlying.obj u)).symm
  · rw [vf_volume_coprod_density_right,rvVolumeLift_density]
    exact (coprod_density_right U V (liftLabelMap V.underlying.obj v)).symm

def volumeLiftCoprodBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection ((rvVolumeLift U).coprod (rvVolumeLift V)) (rvVolumeLift (U.coprod V)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (volumeLiftCoprodMap U V)
    (volume_lift_coprod_map_bijective U V) (fun _ => rfl) (volume_lift_coprod_map_density U V)

def volumeLiftCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeIso ((rvVolumeLift U).coprod (rvVolumeLift V)) (rvVolumeLift (U.coprod V)) :=
  .of_bijection (volumeLiftCoprodBijection hc C U V)

end IntegrationInACVF.Section7
