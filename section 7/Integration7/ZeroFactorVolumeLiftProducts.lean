import Integration7.ZeroFactorVFVolumeIsomorphisms
import Integration7.VolumeLiftProductDomains
import Integration7.ZeroFactorVolumeObjects

/-! Cartesian multiplication by an ordinary degree-zero lift agrees
with the actual RV coefficient product, with unchanged positive density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def volumeLiftZeroProductMap
    (U : PositiveRVVolumeObject (M := M) S n) (Z : RVFiniteObject (M := M) S 0) :
    Map ((rvVolumeLift U).prod_zero Z).domain (rvVolumeLift (U.prod_zero Z)).domain :=
  Map.inclusion (fun p hp => (ordinary_lift_product_domain U.underlying.obj Z.obj p).mpr hp)

theorem volume_lift_zero_product_map_bijective
    (U : PositiveRVVolumeObject (M := M) S n) (Z : RVFiniteObject (M := M) S 0) :
    Function.Bijective (volumeLiftZeroProductMap U Z) := by
  constructor
  · intro p q h
    exact Subtype.ext (congrArg (fun r : (rvVolumeLift (U.prod_zero Z)).domain => r.val) h)
  · intro p
    exact ⟨⟨p.val,(ordinary_lift_product_domain U.underlying.obj Z.obj p.val).mp p.property⟩,rfl⟩

theorem volume_lift_zero_product_map_density
    (U : PositiveRVVolumeObject (M := M) S n) (Z : RVFiniteObject (M := M) S 0)
    (p : ((rvVolumeLift U).prod_zero Z).domain) :
    ((rvVolumeLift U).prod_zero Z).form.value p =
      (rvVolumeLift (U.prod_zero Z)).form.value (volumeLiftZeroProductMap U Z p) := by
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective (rvVolumeLift U).domain (rvLift Z.obj)).2 p
  let u := Map.prodFst (rvVolumeLift U).domain (rvLift Z.obj) uv
  let z := Map.prodSnd (rvVolumeLift U).domain (rvLift Z.obj) uv
  calc
    _ = (rvVolumeLift U).form.value u := positive_vf_zero_product_density_pair (rvVolumeLift U) Z u z
    _ = _ := ?_
  have hLabel : liftLabelMap (U.prod_zero Z).underlying.obj
      (volumeLiftZeroProductMap U Z ((mixedPack (rvVolumeLift U).domain (rvLift Z.obj)).toImage uv)) =
      rvPackPair U.underlying.obj.domain Z.obj.domain (liftLabelMap U.underlying.obj u) (liftLabelMap Z.obj z) :=
    Subtype.ext rfl
  change U.form.value (liftLabelMap U.underlying.obj u) = (U.prod_zero Z).form.value
    (liftLabelMap (U.prod_zero Z).underlying.obj
      (volumeLiftZeroProductMap U Z ((mixedPack (rvVolumeLift U).domain (rvLift Z.obj)).toImage uv)))
  rw [hLabel,positiveZeroProduct_density,rvUnpack_pair]
  rfl

def volumeLiftZeroProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VFVolumeBijection ((rvVolumeLift U).prod_zero Z) (rvVolumeLift (U.prod_zero Z)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (volumeLiftZeroProductMap U Z)
    (volume_lift_zero_product_map_bijective U Z) (fun _ => rfl) (volume_lift_zero_product_map_density U Z)

end IntegrationInACVF.Section7
