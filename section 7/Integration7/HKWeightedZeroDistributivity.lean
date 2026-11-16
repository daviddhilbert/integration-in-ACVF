module

public import Integration7.RVProductCoproductCharts
public import Integration7.HKWeightedZeroBlowups
public import Integration7.VolumeCoproductAssociativity
public import Integration7.RVVolumeInverse

@[expose] public section

/-! Distribution of an ordinary RV[0] factor retains exactly the
positive labels and the density on each summand. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK

set_option allowUnsafeReducibility true in
attribute [local reducible] zeroProduct multiplyForm PositiveRVVolumeObject.zero_prod rvFiniteProductObject PositiveRVVolumeObject.coprod rvFiniteCoprodObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

private theorem zeroProductFold_left
    (Z : ZeroRVVolumeObject (M := M) S) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : (zeroProduct Z U).underlying.obj.domain) :
    (rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map
      (rvCoprodLeftMap (zeroProduct Z U).underlying.obj
        (zeroProduct Z V).underlying.obj x) =
      rvProductMap (Map.id Z.underlying.obj.domain) (rvCoprodLeftMap U.underlying.obj V.underlying.obj) x := by
  change (rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map
    (rvCoprodLeftMap (rvProductObject Z.underlying.obj U.underlying.obj) (rvProductObject Z.underlying.obj V.underlying.obj) x) = _
  exact rvProductCoprodFold_left Z.underlying.obj U.underlying.obj V.underlying.obj x

private theorem zeroProductFold_right
    (Z : ZeroRVVolumeObject (M := M) S) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : (zeroProduct Z V).underlying.obj.domain) :
    (rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map
      (rvCoprodRightMap (zeroProduct Z U).underlying.obj
        (zeroProduct Z V).underlying.obj x) =
      rvProductMap (Map.id Z.underlying.obj.domain) (rvCoprodRightMap U.underlying.obj V.underlying.obj) x := by
  change (rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map
    (rvCoprodRightMap (rvProductObject Z.underlying.obj U.underlying.obj) (rvProductObject Z.underlying.obj V.underlying.obj) x) = _
  exact rvProductCoprodFold_right Z.underlying.obj U.underlying.obj V.underlying.obj x

theorem volumeZeroProductCoprodFold_coordinates
    (Z : ZeroRVVolumeObject (M := M) S) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : ((zeroProduct Z U).coprod (zeroProduct Z V)).underlying.obj.domain) :
    (zeroProduct Z (U.coprod V)).underlying.obj.value
      ((rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map x) =
        ((zeroProduct Z U).coprod (zeroProduct Z V)).underlying.obj.value x := by
  rcases volumeCoprod_cases (zeroProduct Z U) (zeroProduct Z V) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain U.underlying.obj.domain a
    rw [zeroProductFold_left,rvProductMap_pair,zeroProduct_coordinates,
      rvUnpack_pair,rvCoprod_value_left,zeroProduct_coordinates,rvUnpack_pair]
    exact rvCoprod_value_left U.underlying.obj V.underlying.obj u
  · obtain ⟨z,v,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain V.underlying.obj.domain a
    rw [zeroProductFold_right,rvProductMap_pair,zeroProduct_coordinates,
      rvUnpack_pair,rvCoprod_value_right,zeroProduct_coordinates,rvUnpack_pair]
    exact rvCoprod_value_right U.underlying.obj V.underlying.obj v

theorem volumeZeroProductCoprodFold_density
    (Z : ZeroRVVolumeObject (M := M) S) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : ((zeroProduct Z U).coprod (zeroProduct Z V)).underlying.obj.domain) :
    (zeroProduct Z (U.coprod V)).form.value
      ((rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map x) =
        ((zeroProduct Z U).coprod (zeroProduct Z V)).form.value x := by
  rcases volumeCoprod_cases (zeroProduct Z U) (zeroProduct Z V) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain U.underlying.obj.domain a
    rw [zeroProductFold_left,rvProductMap_pair,zeroProduct_density,
      rvUnpack_pair,IntegrationInACVF.Section7.coprod_density_left,zeroProduct_density,rvUnpack_pair]
    exact congrArg (fun t => Z.form.value z * t) (IntegrationInACVF.Section7.coprod_density_left U V u)
  · obtain ⟨z,v,rfl⟩ := exists_rvPackPair Z.underlying.obj.domain V.underlying.obj.domain a
    rw [zeroProductFold_right,rvProductMap_pair,zeroProduct_density,
      rvUnpack_pair,IntegrationInACVF.Section7.coprod_density_right,zeroProduct_density,rvUnpack_pair]
    exact congrArg (fun t => Z.form.value z * t) (IntegrationInACVF.Section7.coprod_density_right U V v)

def volumeZeroProductRightDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : ZeroRVVolumeObject (M := M) (C.base : Set M))
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (zeroProduct Z (U.coprod V))
      ((zeroProduct Z U).coprod (zeroProduct Z V)) := by
  let f := (rvProductCoprodFold Z.underlying.obj U.underlying.obj V.underlying.obj).map
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := ((zeroProduct Z U).coprod (zeroProduct Z V)).underlying.obj)
    (V := (zeroProduct Z (U.coprod V)).underlying.obj) f
    (rvProductCoprodFold_bijective Z.underlying.obj U.underlying.obj V.underlying.obj)
    (volumeZeroProductCoprodFold_coordinates Z U V))
  exact (RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeZeroProductCoprodFold_coordinates Z U V) (volumeZeroProductCoprodFold_density Z U V)).symm hc C

end IntegrationInACVF.Section7.HK
