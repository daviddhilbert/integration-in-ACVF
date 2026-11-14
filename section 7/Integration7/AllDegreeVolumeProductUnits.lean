import Integration7.AllDegreeVolumeData
import Integration7.AllDegreeVolumeProductIsomorphisms
import Section4.RVProductUnits

/-! The ordinary degree-zero singleton is the unit for the original
product in every degree. Density-bearing data handles the zero case uniformly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeProductRightUnitIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) n
      (rvVolumeProduct (C.base : Set M) n 0 U (rvFiniteUnitObject (C.base : Set M))) U := by
  let A := rvVolumeUnderlying (C.base : Set M) n U
  let Z := rvFiniteUnitObject (M := M) (C.base : Set M)
  let D := rvVolumeProductData n 0 U Z
  let E := rvVolumeDataOfObject n U
  let F := rvProductRightUnitMap A.obj
  have hpair (u : A.obj.domain) (z : Z.obj.domain) : F (rvPackPair A.obj.domain Z.obj.domain u z) = u := by
    simp only [F,rvProductRightUnitMap,Map.comp_apply]
    exact congrArg (Map.prodFst A.obj.domain Z.obj.domain) (rvUnpack_pair A.obj.domain Z.obj.domain u z)
  have h : RVVolumeIsoInDegree (C.base : Set M) n D.toObject E.toObject := by
    apply rvVolumeDataRelabelIso hc C D E F (rvProductRightUnitMap_bijective A.obj)
    · intro x
      obtain ⟨u,z,rfl⟩ := exists_rvPackPair A.obj.domain Z.obj.domain x
      change A.obj.value (F (rvPackPair A.obj.domain Z.obj.domain u z)) =
        (rvProductObject A.obj Z.obj).value (rvPackPair A.obj.domain Z.obj.domain u z)
      rw [hpair,rvProductObject_value_pair]
      have hz : Z.obj.value z = Fin.elim0 := funext (fun i => i.elim0)
      rw [hz]
      simp only [rvAppend,Fin.append_elim0,Fin.cast_refl,Function.comp_id]
    · intro x
      obtain ⟨u,z,rfl⟩ := exists_rvPackPair A.obj.domain Z.obj.domain x
      exact (congrArg E.form.value (hpair u z)).trans
        ((mul_one (E.form.value u)).symm.trans (rvVolumeProductData_density_pair n 0 U Z u z).symm)
  simpa only [D,E,rvVolumeProductData_toObject,rvVolumeDataOfObject_toObject] using h

def rvVolumeProductLeftUnitIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) (0+n)
      (rvVolumeProduct (C.base : Set M) 0 n (rvFiniteUnitObject (C.base : Set M)) U)
      ((Nat.zero_add n).symm ▸ U) := by
  let A := rvVolumeUnderlying (C.base : Set M) n U
  let Z := rvFiniteUnitObject (M := M) (C.base : Set M)
  let D := rvVolumeProductData 0 n Z U
  let E := rvVolumeDataOfObject n U
  let F := (rvProductRightUnitMap A.obj).comp (rvProductSwapMap Z.obj A.obj)
  have hF : Function.Bijective F :=
    (rvProductRightUnitMap_bijective A.obj).comp (rvProductSwapMap_bijective Z.obj A.obj)
  have hpair (z : Z.obj.domain) (u : A.obj.domain) : F (rvPackPair Z.obj.domain A.obj.domain z u) = u := by
    simp only [F,Map.comp_apply,rvProductSwapMap_pair,rvProductRightUnitMap]
    exact congrArg (Map.prodFst A.obj.domain Z.obj.domain) (rvUnpack_pair A.obj.domain Z.obj.domain u z)
  have h : RVVolumeIsoInDegree (C.base : Set M) (0+n) D.toObject ((Nat.zero_add n).symm ▸ E.toObject) := by
    apply rvVolumeDataReindexedIso hc C (Nat.zero_add n) D E F hF
    · intro x
      obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain A.obj.domain x
      change A.obj.value (F (rvPackPair Z.obj.domain A.obj.domain z u)) ∘ finCongr (Nat.zero_add n) =
        (rvProductObject Z.obj A.obj).value (rvPackPair Z.obj.domain A.obj.domain z u)
      rw [hpair,rvProductObject_value_pair]
      have hz : Z.obj.value z = Fin.elim0 := funext (fun i => i.elim0)
      rw [hz]
      exact (Fin.elim0_append _).symm
    · intro x
      obtain ⟨z,u,rfl⟩ := exists_rvPackPair Z.obj.domain A.obj.domain x
      exact (congrArg E.form.value (hpair z u)).trans
        ((one_mul (E.form.value u)).symm.trans (rvVolumeProductData_density_pair 0 n Z U z u).symm)
  simpa only [D,E,rvVolumeProductData_toObject,rvVolumeDataOfObject_toObject] using h

end IntegrationInACVF.Section7
