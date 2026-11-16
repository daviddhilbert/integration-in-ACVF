import Integration7.HKVolumeIsoOperations
import Integration7.RVLeftProductCoproductCharts

/-! Left distributivity for the original product in every degree. The
direct fold preserves the volume coordinate order and the density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod productData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def leftProductCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U V : RVVolumeObject (M := M) (C.base : Set M) n)
    (W : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (coprod _ (n+m) (product _ n m U W) (product _ n m V W))
      (product _ n m (coprod _ n U V) W) := by
  let A := underlying (C.base : Set M) n U
  let B := underlying (C.base : Set M) n V
  let L := underlying (C.base : Set M) m W
  let D := productData n m U W
  let E := productData n m V W
  let F := D.coprod E
  let G := productData n m (coprod (C.base : Set M) n U V) W
  let ωW := form (C.base : Set M) m W
  have hD (u : A.obj.domain) (w : L.obj.domain) := productData_density_pair n m U W u w
  have hE (v : B.obj.domain) (w : L.obj.domain) := productData_density_pair n m V W v w
  have hG (z : (underlying (C.base : Set M) n
      (coprod (C.base : Set M) n U V)).obj.domain) (w : L.obj.domain) :=
    productData_density_pair n m (coprod (C.base : Set M) n U V) W z w
  have hL (u : A.obj.domain) := coprod_density_left n U V u
  have hR (v : B.obj.domain) := coprod_density_right n U V v
  have h : rvVolumeIsoInDegree (C.base : Set M) (n+m) (ofData F) (ofData G) := by
    cases n <;> cases m
    all_goals
      apply dataRelabelIso hc C F G (rvLeftProductCoprodFold A.obj B.obj L.obj).map
        (rvLeftProductCoprodFold_bijective A.obj B.obj L.obj)
      · intro x
        change (rvProductObject (rvCoprodObject A.obj B.obj) L.obj).value _ =
          (rvCoprodObject (rvProductObject A.obj L.obj) (rvProductObject B.obj L.obj)).value x
        rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject B.obj L.obj) x
          with ⟨a,rfl⟩ | ⟨a,rfl⟩
        · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
          rw [rvLeftProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
            rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
          rfl
        · obtain ⟨v,w,rfl⟩ := exists_rvPackPair B.obj.domain L.obj.domain a
          rw [rvLeftProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
            rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
          rfl
      · intro x
        rcases rvObjectCoprod_cases (rvProductObject A.obj L.obj) (rvProductObject B.obj L.obj) x
          with ⟨a,rfl⟩ | ⟨a,rfl⟩
        · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
          have he := (rvLeftProductCoprodFold_left A.obj B.obj L.obj (rvPackPair _ _ u w)).trans
            (rvProductMap_pair (rvCoprodLeftMap A.obj B.obj) (Map.id L.obj.domain) u w)
          exact (congrArg G.form.value he).trans
            ((hG (rvCoprodLeftMap A.obj B.obj u) w).trans
              ((congrArg (fun t => t * ωW.value w) (hL u)).trans
                ((hD u w).symm.trans (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u w)).symm)))
        · obtain ⟨v,w,rfl⟩ := exists_rvPackPair B.obj.domain L.obj.domain a
          have he := (rvLeftProductCoprodFold_right A.obj B.obj L.obj (rvPackPair _ _ v w)).trans
            (rvProductMap_pair (rvCoprodRightMap A.obj B.obj) (Map.id L.obj.domain) v w)
          exact (congrArg G.form.value he).trans
            ((hG (rvCoprodRightMap A.obj B.obj v) w).trans
              ((congrArg (fun t => t * ωW.value w) (hR v)).trans
                ((hE v w).symm.trans (RVVolumeData.coprod_density_right D E (rvPackPair _ _ v w)).symm)))
  simpa only [F,G,D,E,data_coprod_ofData,productData_ofData] using h

def productLeftDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U V : RVVolumeObject (M := M) (C.base : Set M) n)
    (W : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (product _ n m (coprod _ n U V) W)
      (coprod _ (n+m) (product _ n m U W) (product _ n m V W)) :=
  isoSymm hc C (n := n+m)
    (U := coprod _ (n+m) (product _ n m U W) (product _ n m V W))
    (V := product _ n m (coprod _ n U V) W) (leftProductCoprodFoldIso hc C U V W)

end IntegrationInACVF.Section7.HK
