import IntegrationSection5.RelativeFibreBijection
import Section5.VerticalConstruction

/-! A vertical root family restricts to the pinned genuine unary root
family on each coordinate fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

def verticalTail (u : Fin (n+1) → VF (M := M)) (t : Fin m → RV (M := M)) : Point (M := M) n m :=
  (fun j => u j.succ,t)

theorem coordinateInsert_unaryPoint (u : Fin (n+1) → VF (M := M)) (x : VF (M := M))
    (t : Fin m → RV (M := M)) :
    coordinateInsert 0 u (unaryPoint x t) = insertHead x (verticalTail u t) := by
  refine Prod.ext ?_ rfl
  funext j
  cases j using Fin.cases with
  | zero => simp [coordinateInsert,unaryPoint,insertHead,vfAt]
  | succ j => simp [coordinateInsert,unaryPoint,insertHead,verticalTail,Fin.succ_ne_zero]

def verticalRootFibre (R : VerticalRootFamily A) (u : Fin (n+1) → VF (M := M)) :
    RootFamily (coordinateFibre A 0 u) where
  set := coordinateFibre R.set 0 u
  subset := fun p hp => R.subset hp
  finite t := by
    have h := R.finite (verticalTail u t)
    apply h.subset
    intro x hx
    change coordinateInsert 0 u (unaryPoint x t) ∈ carrier R.set at hx
    rwa [coordinateInsert_unaryPoint] at hx

theorem verticalRootFibre_fibre (R : VerticalRootFamily A) (u : Fin (n+1) → VF (M := M))
    (t : Fin m → RV (M := M)) :
    (verticalRootFibre R u).fibre t = R.fibre (verticalTail u t) := by
  ext x
  rw [RootFamily.mem_fibre,VerticalRootFamily.mem_fibre]
  change (coordinateInsert 0 u (unaryPoint x t) ∈ carrier R.set) ↔ _
  rw [coordinateInsert_unaryPoint]

theorem verticalRootFibre_bound (R : VerticalRootFamily A) (u : Fin (n+1) → VF (M := M))
    (d : ℕ) (hd : R.Bound d) : (verticalRootFibre R u).Bound d := by
  intro t ht
  rw [verticalRootFibre_fibre] at ht ⊢
  exact hd _ ht

theorem coordinateFibre_tagged (i : Fin (n+1)) (u : Fin (n+1) → VF (M := M)) {k : Fin m}
    (hA : Tagged (carrier A) i k) : Tagged (carrier (coordinateFibre A i u)) 0 k := by
  intro p hp
  have h := hA (coordinateInsert i u p) hp
  simpa only [coordinateInsert,vfAt,Function.update_self] using h

theorem verticalRootFibre_hull (R : VerticalRootFamily A) (u : Fin (n+1) → VF (M := M))
    (p : Point (M := M) 1 m) :
    p ∈ hull (carrier (verticalRootFibre R u).set) ↔ coordinateInsert 0 u p ∈ R.verticalHull := by
  constructor
  · rintro ⟨q,hq,hqp⟩
    have hlabels := ((sameRV_iff _ _).mp hqp).2
    have hrv := ((sameRV_iff _ _).mp hqp).1 0
    refine ⟨vfAt q 0,?_,?_⟩
    · apply (R.mem_fibre _ _).mpr
      change insertHead (vfAt q 0) (dropHead id (coordinateInsert 0 u p)) ∈ carrier R.set
      have he : insertHead (vfAt q 0) (dropHead id (coordinateInsert 0 u p)) = coordinateInsert 0 u q := by
        refine Prod.ext ?_ hlabels.symm
        funext j
        cases j using Fin.cases with
        | zero => simp [insertHead,coordinateInsert,vfAt]
        | succ j => simp [insertHead,dropHead,coordinateInsert,Fin.succ_ne_zero]
      rw [he]
      exact hq
    · simpa only [coordinateInsert,vfAt,Function.update_self] using hrv
  · rintro ⟨x,hx,hxp⟩
    let q : Point (M := M) 1 m := unaryPoint x p.2
    refine ⟨q,?_,?_⟩
    · change coordinateInsert 0 u (unaryPoint x p.2) ∈ carrier R.set
      have he : coordinateInsert 0 u (unaryPoint x p.2) = insertHead x (dropHead id (coordinateInsert 0 u p)) := by
        refine Prod.ext ?_ rfl
        funext j
        cases j using Fin.cases with
        | zero => simp [coordinateInsert,unaryPoint,insertHead,vfAt]
        | succ j => simp [coordinateInsert,unaryPoint,insertHead,dropHead,Fin.succ_ne_zero]
      rw [he]
      exact (R.mem_fibre _ _).mp hx
    · apply (sameRV_iff _ _).mpr
      refine ⟨?_,rfl⟩
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa only [q,unaryPoint,coordinateInsert,vfAt,Function.update_self,Matrix.cons_val_zero] using hxp

end IntegrationInACVF.Section5
