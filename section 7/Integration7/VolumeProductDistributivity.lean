import Integration7.RVProductCoproductCharts
import Integration7.VolumeProductPointwise
import Integration7.VolumeCoproductAssociativity
import Integration7.RVVolumeInverse

/-! Actual distributivity preserves each coordinate and density. No
coordinate block is exchanged in this right-distributivity chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod PositiveRVVolumeObject.coprod
  rvFiniteProductObject rvFiniteCoprodObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

theorem volumeProductCoprodFold_coordinates
    (U : PositiveRVVolumeObject (M := M) S n) (V W : PositiveRVVolumeObject (M := M) S m)
    (x : ((U.prod V).coprod (U.prod W)).underlying.obj.domain) :
    (U.prod (V.coprod W)).underlying.obj.value
      ((rvProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map x) =
        ((U.prod V).coprod (U.prod W)).underlying.obj.value x := by
  change (rvProductObject U.underlying.obj (rvCoprodObject V.underlying.obj W.underlying.obj)).value _ =
    (rvCoprodObject (rvProductObject U.underlying.obj V.underlying.obj)
      (rvProductObject U.underlying.obj W.underlying.obj)).value x
  rcases rvObjectCoprod_cases (rvProductObject U.underlying.obj V.underlying.obj)
    (rvProductObject U.underlying.obj W.underlying.obj) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain a
    rw [rvProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
      rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
    rfl
  · obtain ⟨u,w,rfl⟩ := exists_rvPackPair U.underlying.obj.domain W.underlying.obj.domain a
    rw [rvProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
      rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
    rfl

theorem volumeProductCoprodFold_density
    (U : PositiveRVVolumeObject (M := M) S n) (V W : PositiveRVVolumeObject (M := M) S m)
    (x : ((U.prod V).coprod (U.prod W)).underlying.obj.domain) :
    (U.prod (V.coprod W)).form.value
      ((rvProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map x) =
        ((U.prod V).coprod (U.prod W)).form.value x := by
  rcases volumeCoprod_cases (U.prod V) (U.prod W) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain V.underlying.obj.domain a
    rw [rvProductCoprodFold_left,rvProductMap_pair,positiveProduct_density_pair,
      coprod_density_left,coprod_density_left,positiveProduct_density_pair]
    rfl
  · obtain ⟨u,w,rfl⟩ := exists_rvPackPair U.underlying.obj.domain W.underlying.obj.domain a
    rw [rvProductCoprodFold_right,rvProductMap_pair,positiveProduct_density_pair,
      coprod_density_right,coprod_density_right,positiveProduct_density_pair]
    rfl

def volumeProductCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V W : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIso ((U.prod V).coprod (U.prod W)) (U.prod (V.coprod W)) := by
  let f := (rvProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := ((U.prod V).coprod (U.prod W)).underlying.obj)
    (V := (U.prod (V.coprod W)).underlying.obj) f
    (rvProductCoprodFold_bijective U.underlying.obj V.underlying.obj W.underlying.obj)
    (volumeProductCoprodFold_coordinates U V W))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeProductCoprodFold_coordinates U V W) (volumeProductCoprodFold_density U V W)

def volumeProductRightDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (V W : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIso (U.prod (V.coprod W)) ((U.prod V).coprod (U.prod W)) :=
  (volumeProductCoprodFoldIso hc C U V W).symm hc C

end IntegrationInACVF.Section7
