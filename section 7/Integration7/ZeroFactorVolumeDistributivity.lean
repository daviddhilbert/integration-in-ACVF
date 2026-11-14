import Integration7.RVProductCoproductCharts
import Integration7.ZeroFactorVolumeObjects
import Integration7.VolumeCoproductAssociativity
import Integration7.RVVolumeInverse

/-! Distribution of an ordinary RV[0] factor retains exactly the
positive labels and the density on each summand. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.zero_prod PositiveRVVolumeObject.coprod rvFiniteCoprodObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

private theorem zeroProductFold_left
    (Z : RVFiniteObject (M := M) S 0) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : (PositiveRVVolumeObject.zero_prod Z U).underlying.obj.domain) :
    (rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map
      (rvCoprodLeftMap (PositiveRVVolumeObject.zero_prod Z U).underlying.obj
        (PositiveRVVolumeObject.zero_prod Z V).underlying.obj x) =
      rvProductMap (Map.id Z.obj.domain) (rvCoprodLeftMap U.underlying.obj V.underlying.obj) x := by
  change (rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map
    (rvCoprodLeftMap (rvProductObject Z.obj U.underlying.obj) (rvProductObject Z.obj V.underlying.obj) x) = _
  exact rvProductCoprodFold_left Z.obj U.underlying.obj V.underlying.obj x

private theorem zeroProductFold_right
    (Z : RVFiniteObject (M := M) S 0) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : (PositiveRVVolumeObject.zero_prod Z V).underlying.obj.domain) :
    (rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map
      (rvCoprodRightMap (PositiveRVVolumeObject.zero_prod Z U).underlying.obj
        (PositiveRVVolumeObject.zero_prod Z V).underlying.obj x) =
      rvProductMap (Map.id Z.obj.domain) (rvCoprodRightMap U.underlying.obj V.underlying.obj) x := by
  change (rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map
    (rvCoprodRightMap (rvProductObject Z.obj U.underlying.obj) (rvProductObject Z.obj V.underlying.obj) x) = _
  exact rvProductCoprodFold_right Z.obj U.underlying.obj V.underlying.obj x

theorem volumeZeroProductCoprodFold_coordinates
    (Z : RVFiniteObject (M := M) S 0) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z (U.coprod V)).underlying.obj.value
      ((rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map x) =
        ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)).underlying.obj.value x := by
  rcases volumeCoprod_cases (.zero_prod Z U) (.zero_prod Z V) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain U.underlying.obj.domain a
    rw [zeroProductFold_left,rvProductMap_pair,zeroPositiveProduct_coordinates,
      rvUnpack_pair,rvCoprod_value_left,zeroPositiveProduct_coordinates,rvUnpack_pair]
    exact rvCoprod_value_left U.underlying.obj V.underlying.obj u
  · obtain ⟨z,v,rfl⟩ := exists_rvPackPair Z.obj.domain V.underlying.obj.domain a
    rw [zeroProductFold_right,rvProductMap_pair,zeroPositiveProduct_coordinates,
      rvUnpack_pair,rvCoprod_value_right,zeroPositiveProduct_coordinates,rvUnpack_pair]
    exact rvCoprod_value_right U.underlying.obj V.underlying.obj v

theorem volumeZeroProductCoprodFold_density
    (Z : RVFiniteObject (M := M) S 0) (U V : PositiveRVVolumeObject (M := M) S k)
    (x : ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)).underlying.obj.domain) :
    (PositiveRVVolumeObject.zero_prod Z (U.coprod V)).form.value
      ((rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map x) =
        ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)).form.value x := by
  rcases volumeCoprod_cases (.zero_prod Z U) (.zero_prod Z V) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain U.underlying.obj.domain a
    rw [zeroProductFold_left,rvProductMap_pair,zeroPositiveProduct_density,
      rvUnpack_pair,coprod_density_left,zeroPositiveProduct_density,rvUnpack_pair]
    exact coprod_density_left U V u
  · obtain ⟨z,v,rfl⟩ := exists_rvPackPair Z.obj.domain V.underlying.obj.domain a
    rw [zeroProductFold_right,rvProductMap_pair,zeroPositiveProduct_density,
      rvUnpack_pair,coprod_density_right,zeroPositiveProduct_density,rvUnpack_pair]
    exact coprod_density_right U V v

def volumeZeroProductRightDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Z : RVFiniteObject (M := M) (C.base : Set M) 0)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (PositiveRVVolumeObject.zero_prod Z (U.coprod V))
      ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)) := by
  let f := (rvProductCoprodFold Z.obj U.underlying.obj V.underlying.obj).map
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := ((PositiveRVVolumeObject.zero_prod Z U).coprod (.zero_prod Z V)).underlying.obj)
    (V := (PositiveRVVolumeObject.zero_prod Z (U.coprod V)).underlying.obj) f
    (rvProductCoprodFold_bijective Z.obj U.underlying.obj V.underlying.obj)
    (volumeZeroProductCoprodFold_coordinates Z U V))
  exact (RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeZeroProductCoprodFold_coordinates Z U V) (volumeZeroProductCoprodFold_density Z U V)).symm hc C

end IntegrationInACVF.Section7
