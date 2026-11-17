module

public import Integration7.HKWeightedVFZeroIsomorphisms
public import Integration7.HKRVProductBridges
public import Integration7.ZeroFactorVolumeLiftProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The lift preserves the actual product with a weighted zero factor.
Its literal mixed-domain identity retains the product of both RV forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def weightedLiftZeroProductMap
    (U : PositiveRVVolumeObject (M := M) S n) (Z : ZeroRVVolumeObject (M := M) S) :
    Map (positiveVFZeroProduct (rvVolumeLift U) Z).domain (rvVolumeLift (positiveZeroProduct U Z)).domain :=
  Map.inclusion (fun p hp => (ordinary_lift_product_domain U.underlying.obj Z.underlying.obj p).mpr hp)

theorem weighted_lift_zero_product_map_bijective
    (U : PositiveRVVolumeObject (M := M) S n) (Z : ZeroRVVolumeObject (M := M) S) :
    Function.Bijective (weightedLiftZeroProductMap U Z) :=
  volume_lift_zero_product_map_bijective U Z.underlying

theorem weighted_lift_zero_product_map_density
    (U : PositiveRVVolumeObject (M := M) S n) (Z : ZeroRVVolumeObject (M := M) S)
    (p : (positiveVFZeroProduct (rvVolumeLift U) Z).domain) :
    (positiveVFZeroProduct (rvVolumeLift U) Z).form.value p =
      (rvVolumeLift (positiveZeroProduct U Z)).form.value (weightedLiftZeroProductMap U Z p) := by
  obtain ⟨uv,rfl⟩ := (mixedPackToImage_bijective (rvVolumeLift U).domain (rvLift Z.underlying.obj)).2 p
  let u := Map.prodFst (rvVolumeLift U).domain (rvLift Z.underlying.obj) uv
  let z := Map.prodSnd (rvVolumeLift U).domain (rvLift Z.underlying.obj) uv
  calc
    _ = (rvVolumeLift U).form.value u * (zeroLift Z).form.value z :=
      positiveVFZeroProduct_density_pair (rvVolumeLift U) Z u z
    _ = _ := ?_
  have hLabel : liftLabelMap (positiveZeroProduct U Z).underlying.obj
      (weightedLiftZeroProductMap U Z ((mixedPack (rvVolumeLift U).domain (rvLift Z.underlying.obj)).toImage uv)) =
      rvPackPair U.underlying.obj.domain Z.underlying.obj.domain
        (liftLabelMap U.underlying.obj u) (liftLabelMap Z.underlying.obj z) := Subtype.ext rfl
  change U.form.value (liftLabelMap U.underlying.obj u) * Z.form.value (liftLabelMap Z.underlying.obj z) =
    (positiveZeroProduct U Z).form.value
      (liftLabelMap (positiveZeroProduct U Z).underlying.obj
        (weightedLiftZeroProductMap U Z
          ((mixedPack (rvVolumeLift U).domain (rvLift Z.underlying.obj)).toImage uv)))
  rw [hLabel,positiveZeroProduct_density,rvUnpack_pair]
  rfl

def weightedLiftZeroProductBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VFVolumeBijection (positiveVFZeroProduct (rvVolumeLift U) Z) (rvVolumeLift (positiveZeroProduct U Z)) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (weightedLiftZeroProductMap U Z)
    (weighted_lift_zero_product_map_bijective U Z) (fun _ => rfl) (weighted_lift_zero_product_map_density U Z)

end IntegrationInACVF.Section7.HK
