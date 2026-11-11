import IntegrationSection5.RelativelyUnary
import Section5.TransformGeometry
import IntegrationSection3.CoordinateSlices

/-! Actual coordinate fibres. Only the other VF coordinates are named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def coordinateInsert (i : Fin n) (u : Fin n → VF (M := M)) (p : Point (M := M) 1 m) :
    Point (M := M) n m := (Function.update u i (vfAt p 0),p.2)

def coordinateProject (i : Fin n) (p : Point (M := M) n m) : Point (M := M) 1 m :=
  (fun _ => vfAt p i,p.2)

theorem coordinateProject_insert (i : Fin n) (u : Fin n → VF (M := M))
    (p : Point (M := M) 1 m) : coordinateProject i (coordinateInsert i u p) = p := by
  refine Prod.ext ?_ rfl
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Function.update_self i (vfAt p 0) u

theorem coordinateInsert_project (i : Fin n) (u : Fin n → VF (M := M))
    (p : Point (M := M) n m) (hp : ∀ j, j ≠ i → vfAt p j = u j) :
    coordinateInsert i u (coordinateProject i p) = p := by
  refine Prod.ext ?_ rfl
  funext j
  by_cases hj : j = i
  · subst j
    exact Function.update_self i (vfAt p i) u
  · exact (Function.update_of_ne hj _ _).trans (hp j hj).symm

theorem coordinateInsert_injective (i : Fin n) (u : Fin n → VF (M := M)) :
    Function.Injective (coordinateInsert (m := m) i u) := by
  intro p q he
  have h := congrArg (coordinateProject i) he
  rw [coordinateProject_insert,coordinateProject_insert] at h
  exact h

theorem coordinateInsert_sameRV (i : Fin n) (u : Fin n → VF (M := M))
    {p q : Point (M := M) 1 m} (hpq : SameRV p q) :
    SameRV (coordinateInsert i u p) (coordinateInsert i u q) := by
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,((sameRV_iff _ _).mp hpq).2⟩
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [coordinateInsert,vfAt,Function.update_self] using ((sameRV_iff _ _).mp hpq).1 0
  · simp only [coordinateInsert,Function.update_of_ne hj]

def coordinateFibreBase (S : Set M) (i : Fin n) (u : Fin n → VF (M := M)) : Set M :=
  S ∪ Set.range (fun j : CoordinateSlices.Other i => (u j.val).val)

end IntegrationInACVF.Section5
