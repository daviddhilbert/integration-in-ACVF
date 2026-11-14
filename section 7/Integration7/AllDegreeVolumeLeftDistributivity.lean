import Integration7.AllDegreeVolumeCoproductData
import Integration7.AllDegreeVolumeIsoOperations
import Integration7.RVLeftProductCoproductCharts

/-! Left distributivity for the original product in every degree. The
direct fold preserves the volume coordinate order and the density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

set_option allowUnsafeReducibility true in
attribute [local reducible] RVVolumeData.coprod rvVolumeProductData rvFiniteProductObject
  rvFiniteCoprodObject rvCoprodObject rvProductObject

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeLeftProductCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U V : RVVolumeObject (M := M) (C.base : Set M) n)
    (W : RVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U W) (rvVolumeProduct _ n m V W))
      (rvVolumeProduct _ n m (rvVolumeCoprod _ n U V) W) := by
  let A := rvVolumeUnderlying (C.base : Set M) n U
  let B := rvVolumeUnderlying (C.base : Set M) n V
  let L := rvVolumeUnderlying (C.base : Set M) m W
  let D := rvVolumeProductData n m U W
  let E := rvVolumeProductData n m V W
  let F := D.coprod E
  let G := rvVolumeProductData n m (rvVolumeCoprod (C.base : Set M) n U V) W
  let ωW := rvVolumeForm (C.base : Set M) m W
  have hD (u : A.obj.domain) (w : L.obj.domain) := rvVolumeProductData_density_pair n m U W u w
  have hE (v : B.obj.domain) (w : L.obj.domain) := rvVolumeProductData_density_pair n m V W v w
  have hG (z : (rvVolumeUnderlying (C.base : Set M) n
      (rvVolumeCoprod (C.base : Set M) n U V)).obj.domain) (w : L.obj.domain) :=
    rvVolumeProductData_density_pair n m (rvVolumeCoprod (C.base : Set M) n U V) W z w
  have hL (u : A.obj.domain) := rvVolumeCoprod_density_left n U V u
  have hR (v : B.obj.domain) := rvVolumeCoprod_density_right n U V v
  have h : RVVolumeIsoInDegree (C.base : Set M) (n+m) F.toObject G.toObject := by
    cases n <;> cases m
    all_goals
      apply rvVolumeDataRelabelIso hc C F G (rvLeftProductCoprodFold A.obj B.obj L.obj).map
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
  simpa only [F,G,D,E,RVVolumeData.coprod_toObject,rvVolumeProductData_toObject] using h

def rvVolumeProductLeftDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U V : RVVolumeObject (M := M) (C.base : Set M) n)
    (W : RVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeProduct _ n m (rvVolumeCoprod _ n U V) W)
      (rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U W) (rvVolumeProduct _ n m V W)) :=
  rvVolumeIsoSymm hc C (n := n+m)
    (U := rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U W) (rvVolumeProduct _ n m V W))
    (V := rvVolumeProduct _ n m (rvVolumeCoprod _ n U V) W) (rvVolumeLeftProductCoprodFoldIso hc C U V W)

end IntegrationInACVF.Section7
