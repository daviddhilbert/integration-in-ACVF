import Integration7.HKVolumeIsoOperations
import Integration7.RVProductCoproductCharts

/-! Right distributivity for the original product in every degree.
The actual fold retains every volume coordinate and the density on its summand. -/

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

def productCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V W : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (coprod _ (n+m) (product _ n m U V) (product _ n m U W))
      (product _ n m U (coprod _ m V W)) := by
  let A := underlying (C.base : Set M) n U
  let B := underlying (C.base : Set M) m V
  let L := underlying (C.base : Set M) m W
  let D := productData n m U V
  let E := productData n m U W
  let F := D.coprod E
  let G := productData n m U (coprod (C.base : Set M) m V W)
  let ωU := form (C.base : Set M) n U
  have hD (u : A.obj.domain) (v : B.obj.domain) := productData_density_pair n m U V u v
  have hE (u : A.obj.domain) (w : L.obj.domain) := productData_density_pair n m U W u w
  have hG (u : A.obj.domain) (z : (underlying (C.base : Set M) m
      (coprod (C.base : Set M) m V W)).obj.domain) :=
    productData_density_pair n m U (coprod (C.base : Set M) m V W) u z
  have hL (v : B.obj.domain) := coprod_density_left m V W v
  have hR (w : L.obj.domain) := coprod_density_right m V W w
  have h : rvVolumeIsoInDegree (C.base : Set M) (n+m) (ofData F) (ofData G) := by
    cases n <;> cases m
    all_goals
      apply dataRelabelIso hc C F G (rvProductCoprodFold A.obj B.obj L.obj).map
        (rvProductCoprodFold_bijective A.obj B.obj L.obj)
      · intro x
        change (rvProductObject A.obj (rvCoprodObject B.obj L.obj)).value _ =
          (rvCoprodObject (rvProductObject A.obj B.obj) (rvProductObject A.obj L.obj)).value x
        rcases rvObjectCoprod_cases (rvProductObject A.obj B.obj) (rvProductObject A.obj L.obj) x
          with ⟨a,rfl⟩ | ⟨a,rfl⟩
        · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain B.obj.domain a
          rw [rvProductCoprodFold_left,rvProductMap_pair,rvProductObject_value_pair,
            rvCoprod_value_left,rvCoprod_value_left,rvProductObject_value_pair]
          rfl
        · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
          rw [rvProductCoprodFold_right,rvProductMap_pair,rvProductObject_value_pair,
            rvCoprod_value_right,rvCoprod_value_right,rvProductObject_value_pair]
          rfl
      · intro x
        rcases rvObjectCoprod_cases (rvProductObject A.obj B.obj) (rvProductObject A.obj L.obj) x
          with ⟨a,rfl⟩ | ⟨a,rfl⟩
        · obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.obj.domain B.obj.domain a
          have he := (rvProductCoprodFold_left A.obj B.obj L.obj (rvPackPair _ _ u v)).trans
            (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodLeftMap B.obj L.obj) u v)
          exact (congrArg G.form.value he).trans
            ((hG u (rvCoprodLeftMap B.obj L.obj v)).trans
              ((congrArg (fun t => ωU.value u * t) (hL v)).trans
                ((hD u v).symm.trans (RVVolumeData.coprod_density_left D E (rvPackPair _ _ u v)).symm)))
        · obtain ⟨u,w,rfl⟩ := exists_rvPackPair A.obj.domain L.obj.domain a
          have he := (rvProductCoprodFold_right A.obj B.obj L.obj (rvPackPair _ _ u w)).trans
            (rvProductMap_pair (Map.id A.obj.domain) (rvCoprodRightMap B.obj L.obj) u w)
          exact (congrArg G.form.value he).trans
            ((hG u (rvCoprodRightMap B.obj L.obj w)).trans
              ((congrArg (fun t => ωU.value u * t) (hR w)).trans
                ((hE u w).symm.trans (RVVolumeData.coprod_density_right D E (rvPackPair _ _ u w)).symm)))
  simpa only [F,G,D,E,data_coprod_ofData,productData_ofData] using h

def productRightDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V W : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (product _ n m U (coprod _ m V W))
      (coprod _ (n+m) (product _ n m U V) (product _ n m U W)) :=
  isoSymm hc C (n := n+m)
    (U := coprod _ (n+m) (product _ n m U V) (product _ n m U W))
    (V := product _ n m U (coprod _ m V W)) (productCoprodFoldIso hc C U V W)

end IntegrationInACVF.Section7.HK
