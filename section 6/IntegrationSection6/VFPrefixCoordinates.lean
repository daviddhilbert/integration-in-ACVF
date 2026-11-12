import IntegrationSection5.RelativeFibreGeometry

/-! Insert and project an active VF prefix while freezing a complementary
VF tuple. The ambient arity n+p is chosen to commute with head deletion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n p m : ℕ}

def vfPrefixTuple (x : Fin n → VF (M := M)) (y : Fin p → VF (M := M)) : Fin (n+p) → VF (M := M) :=
  fun j => if h : j.val < p then y ⟨j.val,h⟩ else x ⟨j.val-p,by omega⟩

def vfPrefixInsert (x : Fin n → VF (M := M)) (q : Point (M := M) p m) : Point (M := M) (n+p) m :=
  (vfPrefixTuple x q.1,q.2)

def vfPrefixProject (q : Point (M := M) (n+p) m) : Point (M := M) p m :=
  (fun j => q.1 ⟨j.val,by omega⟩,q.2)

def VFPrefixTailFixed (x : Fin n → VF (M := M)) (q : Point (M := M) (n+p) m) : Prop :=
  ∀ j : Fin n, q.1 ⟨p+j.val,by omega⟩ = x j

theorem vfPrefixTuple_head (x : Fin n → VF (M := M)) (y : Fin p → VF (M := M)) (j : Fin p) :
    vfPrefixTuple x y ⟨j.val,by omega⟩ = y j := by
  simp only [vfPrefixTuple,dite_eq_left j.isLt]

theorem vfPrefixTuple_tail (x : Fin n → VF (M := M)) (y : Fin p → VF (M := M)) (j : Fin n) :
    vfPrefixTuple x y ⟨p+j.val,by omega⟩ = x j := by
  unfold vfPrefixTuple
  rw [dite_eq_right (show ¬p+j.val < p by omega)]
  congr 1
  apply Fin.ext
  simp

theorem vfPrefixProject_insert (x : Fin n → VF (M := M)) (q : Point (M := M) p m) :
    vfPrefixProject (vfPrefixInsert x q) = q := by
  refine Prod.ext ?_ rfl
  funext j
  exact vfPrefixTuple_head x q.1 j

theorem vfPrefixInsert_injective (x : Fin n → VF (M := M)) : Function.Injective (vfPrefixInsert (p := p) (m := m) x) := by
  intro q r h
  have h' := congrArg vfPrefixProject h
  simpa only [vfPrefixProject_insert] using h'

theorem vfPrefixInsert_project (x : Fin n → VF (M := M)) (q : Point (M := M) (n+p) m)
    (h : VFPrefixTailFixed x q) : vfPrefixInsert x (vfPrefixProject q) = q := by
  refine Prod.ext ?_ rfl
  funext j
  by_cases hj : j.val < p
  · simp only [vfPrefixInsert,vfPrefixTuple,vfPrefixProject,dite_eq_left hj]
  · change vfPrefixTuple x (vfPrefixProject q).1 j = q.1 j
    rw [vfPrefixTuple,dite_eq_right hj]
    exact (h ⟨j.val-p,by omega⟩).symm.trans (congrArg q.1 (Fin.ext (by dsimp; omega)))

theorem vfPrefixTuple_cons (x : Fin n → VF (M := M)) (y : Fin (p+1) → VF (M := M)) :
    vfPrefixTuple x y = Fin.cons (y 0) (vfPrefixTuple x (fun j => y j.succ)) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [vfPrefixTuple]
  | succ j =>
    simp only [Fin.cons_succ]
    by_cases hj : j.val < p
    · have hj' : j.succ.val < p+1 := by simpa only [Fin.val_succ] using Nat.succ_lt_succ hj
      unfold vfPrefixTuple
      rw [dite_eq_left hj',dite_eq_left hj]
      rfl
    · have hj' : ¬j.succ.val < p+1 := by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using hj
      unfold vfPrefixTuple
      rw [dite_eq_right hj',dite_eq_right hj]
      congr 1
      apply Fin.ext
      change (j.val+1)-(p+1) = j.val-p
      omega

theorem vfPrefixInsert_replace (x : Fin n → VF (M := M)) (q : Point (M := M) (p+1) m)
    (z : VF (M := M)) :
    vfPrefixInsert x (replace 0 q z) = replace 0 (vfPrefixInsert x q) z := by
  refine Prod.ext ?_ rfl
  change vfPrefixTuple x (Function.update q.1 0 z) = Function.update (vfPrefixTuple x q.1) 0 z
  rw [vfPrefixTuple_cons,vfPrefixTuple_cons]
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ,Function.update_of_ne (Fin.succ_ne_zero j)]
    congr 1

end IntegrationInACVF.Section6
