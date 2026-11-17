module

public import Integration7.VolumeLiftProductDomains
public import Integration7.PositiveVFVolumeProducts
public import Integration7.GradedVolumeProducts
public import Integration7.VFVolumeIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Cartesian product of full volume lifts is volume
bijective to the lift of the actual RV product, with the original forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def volumeLiftProductMap
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Map ((rvVolumeLift U).prod (rvVolumeLift V)).domain (rvVolumeLift (U.prod V)).domain :=
  Map.inclusion (fun p hp => (ordinary_lift_product_domain U.underlying.obj V.underlying.obj p).mpr hp)

theorem volume_lift_product_map_bijective
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    Function.Bijective (volumeLiftProductMap U V) := by
  constructor
  · intro p q h
    exact Subtype.ext (congrArg (fun r : (rvVolumeLift (U.prod V)).domain => r.val) h)
  · intro p
    exact ⟨⟨p.val,(ordinary_lift_product_domain U.underlying.obj V.underlying.obj p.val).mp p.property⟩,rfl⟩

theorem volume_lift_product_map_density
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m)
    (p : ((rvVolumeLift U).prod (rvVolumeLift V)).domain) :
    ((rvVolumeLift U).prod (rvVolumeLift V)).form.value p =
      (rvVolumeLift (U.prod V)).form.value (volumeLiftProductMap U V p) := by
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective (rvVolumeLift U).domain (rvVolumeLift V).domain).2 p
  let u := Map.prodFst (rvVolumeLift U).domain (rvVolumeLift V).domain uv
  let v := Map.prodSnd (rvVolumeLift U).domain (rvVolumeLift V).domain uv
  calc
    _ = (rvVolumeLift U).form.value u * (rvVolumeLift V).form.value v :=
      positive_vf_volume_product_density (rvVolumeLift U) (rvVolumeLift V) u v
    _ = _ := ?_
  have hLabel : liftLabelMap (U.prod V).underlying.obj
      (volumeLiftProductMap U V ((mixedPack (rvVolumeLift U).domain (rvVolumeLift V).domain).toImage uv)) =
      rvPackPair U.underlying.obj.domain V.underlying.obj.domain
        (liftLabelMap U.underlying.obj u) (liftLabelMap V.underlying.obj v) := Subtype.ext rfl
  change U.form.value (liftLabelMap U.underlying.obj u) *
    V.form.value (liftLabelMap V.underlying.obj v) =
    (U.prod V).form.value (liftLabelMap (U.prod V).underlying.obj
      (volumeLiftProductMap U V ((mixedPack (rvVolumeLift U).domain (rvVolumeLift V).domain).toImage uv)))
  rw [hLabel]
  change _ = (U.form.prod V.form).value (rvUnpack U.underlying.obj.domain V.underlying.obj.domain
    (rvPackPair U.underlying.obj.domain V.underlying.obj.domain
      (liftLabelMap U.underlying.obj u) (liftLabelMap V.underlying.obj v)))
  rw [rvUnpack_pair]
  rfl

def volumeLiftProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    VFVolumeBijection ((rvVolumeLift U).prod (rvVolumeLift V)) (rvVolumeLift (U.prod V)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (volumeLiftProductMap U V)
    (volume_lift_product_map_bijective U V) (fun _ => rfl) (volume_lift_product_map_density U V)

def volumeLiftProductIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    VFVolumeIso ((rvVolumeLift U).prod (rvVolumeLift V)) (rvVolumeLift (U.prod V)) :=
  .of_bijection (volumeLiftProductBijection hc C U V)

end IntegrationInACVF.Section7
