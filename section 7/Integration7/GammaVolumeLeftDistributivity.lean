import Integration7.VolumeProductDistributivity
import Integration7.RVLeftProductCoproductCharts
import Integration7.GammaNamedRVProductDistributivity
import Integration7.GammaNamedPositiveProductIsos
import Integration7.GammaNamedBlowupProducts

/-! Left distributivity of positive volume products over coproducts, `(U ⊔ V) × W ≅ U×W ⊔ V×W`,
preserving coordinates and densities, with a Gamma graph. -/
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

theorem volumeLeftProductCoprodFold_coordinates
    (U V : PositiveRVVolumeObject (M := M) S n) (W : PositiveRVVolumeObject (M := M) S m)
    (x : ((U.prod W).coprod (V.prod W)).underlying.obj.domain) :
    ((U.coprod V).prod W).underlying.obj.value
      ((rvLeftProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map x) =
        ((U.prod W).coprod (V.prod W)).underlying.obj.value x := by
  change (rvProductObject (rvCoprodObject U.underlying.obj V.underlying.obj) W.underlying.obj).value _ =
    (rvCoprodObject (rvProductObject U.underlying.obj W.underlying.obj)
      (rvProductObject V.underlying.obj W.underlying.obj)).value x
  rcases rvObjectCoprod_cases (rvProductObject U.underlying.obj W.underlying.obj)
    (rvProductObject V.underlying.obj W.underlying.obj) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨u,w,rfl⟩ := exists_rvPackPair U.underlying.obj.domain W.underlying.obj.domain a
    rw [rvLeftProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
      rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
    rfl
  · obtain ⟨v,w,rfl⟩ := exists_rvPackPair V.underlying.obj.domain W.underlying.obj.domain a
    rw [rvLeftProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
      rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
    rfl

theorem volumeLeftProductCoprodFold_density
    (U V : PositiveRVVolumeObject (M := M) S n) (W : PositiveRVVolumeObject (M := M) S m)
    (x : ((U.prod W).coprod (V.prod W)).underlying.obj.domain) :
    ((U.coprod V).prod W).form.value
      ((rvLeftProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map x) =
        ((U.prod W).coprod (V.prod W)).form.value x := by
  rcases volumeCoprod_cases (U.prod W) (V.prod W) x with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · obtain ⟨u,w,rfl⟩ := exists_rvPackPair U.underlying.obj.domain W.underlying.obj.domain a
    rw [rvLeftProductCoprodFold_left,rvProductMap_pair,positiveProduct_density_pair,
      coprod_density_left,coprod_density_left,positiveProduct_density_pair]
    rfl
  · obtain ⟨v,w,rfl⟩ := exists_rvPackPair V.underlying.obj.domain W.underlying.obj.domain a
    rw [rvLeftProductCoprodFold_right,rvProductMap_pair,positiveProduct_density_pair,
      coprod_density_right,coprod_density_right,positiveProduct_density_pair]
    rfl

def volumeLeftProductCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) n)
    (W : PositiveRVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIso ((U.prod W).coprod (V.prod W)) ((U.coprod V).prod W) := by
  let f := (rvLeftProductCoprodFold U.underlying.obj V.underlying.obj W.underlying.obj).map
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := ((U.prod W).coprod (V.prod W)).underlying.obj)
    (V := ((U.coprod V).prod W).underlying.obj) f
    (rvLeftProductCoprodFold_bijective U.underlying.obj V.underlying.obj W.underlying.obj)
    (volumeLeftProductCoprodFold_coordinates U V W))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e
    (volumeLeftProductCoprodFold_coordinates U V W) (volumeLeftProductCoprodFold_density U V W)

variable {B : SpecialTransformations.Section3.GammaParameters.Base (M := M)}

theorem gamma_volume_left_product_coprod_fold_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    {W : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hW : VolumeObjectGamma W B) :
    (volumeLeftProductCoprodFoldIso hc C U V W).GammaDefinable B := by
  have hUW := hU.prod hc hW
  have hVW := hV.prod hc hW
  exact gamma_volume_iso_of_preserving_coordinates_full hc C _
    (volumeLeftProductCoprodFold_coordinates U V W) (volumeLeftProductCoprodFold_density U V W)
    (gamma_essential_volume_domain _ (hUW.coprod hVW).coordinates)
    ((gamma_rv_left_product_coprod_fold hc U.underlying.obj V.underlying.obj W.underlying.obj
      hU.domain_graph hV.domain_graph hW.domain_graph).congr (fun _ => rfl))

end IntegrationInACVF.Section7
