import Integration7.AllDegreeVolumeCoproductData
import Integration7.AllDegreeVolumeIsoOperations
import Integration7.RVProductCoproductCharts

/-! Right distributivity for the original product in every degree.
The actual fold retains every volume coordinate and the density on its summand. -/

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

def rvVolumeProductCoprodFoldIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V W : RVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U V) (rvVolumeProduct _ n m U W))
      (rvVolumeProduct _ n m U (rvVolumeCoprod _ m V W)) := by
  let A := rvVolumeUnderlying (C.base : Set M) n U
  let B := rvVolumeUnderlying (C.base : Set M) m V
  let L := rvVolumeUnderlying (C.base : Set M) m W
  let D := rvVolumeProductData n m U V
  let E := rvVolumeProductData n m U W
  let F := D.coprod E
  let G := rvVolumeProductData n m U (rvVolumeCoprod (C.base : Set M) m V W)
  let ωU := rvVolumeForm (C.base : Set M) n U
  have hD (u : A.obj.domain) (v : B.obj.domain) := rvVolumeProductData_density_pair n m U V u v
  have hE (u : A.obj.domain) (w : L.obj.domain) := rvVolumeProductData_density_pair n m U W u w
  have hG (u : A.obj.domain) (z : (rvVolumeUnderlying (C.base : Set M) m
      (rvVolumeCoprod (C.base : Set M) m V W)).obj.domain) :=
    rvVolumeProductData_density_pair n m U (rvVolumeCoprod (C.base : Set M) m V W) u z
  have hL (v : B.obj.domain) := rvVolumeCoprod_density_left m V W v
  have hR (w : L.obj.domain) := rvVolumeCoprod_density_right m V W w
  have h : RVVolumeIsoInDegree (C.base : Set M) (n+m) F.toObject G.toObject := by
    cases n <;> cases m
    all_goals
      apply rvVolumeDataRelabelIso hc C F G (rvProductCoprodFold A.obj B.obj L.obj).map
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
  simpa only [F,G,D,E,RVVolumeData.coprod_toObject,rvVolumeProductData_toObject] using h

def rvVolumeProductRightDistribIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n)
    (V W : RVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeProduct _ n m U (rvVolumeCoprod _ m V W))
      (rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U V) (rvVolumeProduct _ n m U W)) :=
  rvVolumeIsoSymm hc C (n := n+m)
    (U := rvVolumeCoprod _ (n+m) (rvVolumeProduct _ n m U V) (rvVolumeProduct _ n m U W))
    (V := rvVolumeProduct _ n m U (rvVolumeCoprod _ m V W)) (rvVolumeProductCoprodFoldIso hc C U V W)

end IntegrationInACVF.Section7
