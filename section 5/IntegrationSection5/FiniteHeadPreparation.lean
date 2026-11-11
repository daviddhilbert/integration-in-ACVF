import IntegrationSection5.RelativeInverseSlices
import IntegrationSection5.RVCellInfinite

/-! Finite coordinate fibres are encoded by retained RV labels after actual
relative preparation. No finite-choice or separation conclusion is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.HeadPreparation
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

/-- Each fixed complementary VF tuple and old RV tuple has finitely many heads. -/
def FiniteHeadFibres (A : DefSet (M := M) S (n+1) m) : Prop :=
  ∀ p : Point (M := M) n m, {x : VF (M := M) | insertHead x p ∈ carrier A}.Finite

theorem finite_fibres_target_head_zero (T : HeadPreparation A) (hA : FiniteHeadFibres A)
    (b : T.target) : vfAt b.val 0 = 0 := by
  by_contra hb
  let a₀ := T.inverseMap b
  let g : VF (M := M) → VF (M := M) := fun x => vfAt a₀.val 0+x-vfAt b.val 0
  have hg : Function.Injective g := by
    intro x y hxy
    exact add_left_cancel (sub_left_inj.mp hxy)
  have hFin := (hA (dropHead id a₀.val)).preimage hg.injOn
  apply nonzero_rv_class_infinite (vfAt b.val 0) hb
  apply hFin.subset
  intro x hx
  let q : Point (M := M) (n+1) T.arity := replace 0 b.val x
  have hq : q ∈ carrier T.target := T.saturated b.val b.property x hx
  let c : T.target := ⟨q,hq⟩
  have htail : TailEq c.val b.val := by
    intro j
    simp [c,q,replace,vfAt,Fin.succ_ne_zero]
  have hdiff := T.inverse_difference c b htail rfl
  have hlabels := T.inverse_labels c b rfl
  have he : insertHead (g x) (dropHead id a₀.val) = (T.inverseMap c).val := by
    refine Prod.ext ?_ hlabels.symm
    funext j
    cases j using Fin.cases with
    | zero =>
      change vfAt a₀.val 0+x-vfAt b.val 0 = vfAt (T.inverseMap c).val 0
      change vfAt (T.inverseMap c).val 0-vfAt a₀.val 0 = x-vfAt b.val 0 at hdiff
      linear_combination -hdiff
    | succ j =>
      change vfAt a₀.val j.succ = vfAt (T.inverseMap c).val j.succ
      exact (T.inverse_tail b j).trans ((htail j).symm.trans (T.inverse_tail c j).symm)
  change insertHead (g x) (dropHead id a₀.val) ∈ carrier A
  rw [he]
  exact (T.inverseMap c).property

/-- On a finite-fibre family, the retained labels separate the original head. -/
theorem finite_fibres_labels_separate (T : HeadPreparation A) (hA : FiniteHeadFibres A)
    (a b : A) (ht : TailEq a.val b.val) (hl : (T.map a).val.2 = (T.map b).val.2) : a = b := by
  apply T.bijective.1
  apply Subtype.ext
  refine Prod.ext ?_ hl
  funext j
  cases j using Fin.cases with
  | zero =>
    exact (T.finite_fibres_target_head_zero hA (T.map a)).trans
      (T.finite_fibres_target_head_zero hA (T.map b)).symm
  | succ j =>
    exact (T.special.choose a j.succ (Fin.succ_ne_zero j)).trans
      ((ht j).trans (T.special.choose b j.succ (Fin.succ_ne_zero j)).symm)

end IntegrationInACVF.Section5.HeadPreparation
