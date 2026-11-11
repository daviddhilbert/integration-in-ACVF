import IntegrationSection3ACVF.FiniteOrderIntervalPatterns
import Mathlib.Order.Interval.Set.OrdConnected

/-! Nonpoint cells of a finite actual endpoint partition. Their finite
index is the tuple of comparison signs against the endpoints. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderCells

variable {α : Type*} [LinearOrder α]

abbrev Code (F : Finset α) := F → Bool × Bool

noncomputable def code (F : Finset α) (x : α) : Code F :=
  fun t => (decide (x < t.val),decide (t.val < x))

def cell (F : Finset α) (c : Code F) : Set α := {x | x ∉ F ∧ code F x = c}

theorem code_eq_iff (F : Finset α) (x y : α) : code F x = code F y ↔ FiniteOrder.Pattern F x y := by
  constructor
  · intro h t ht
    have he := congrFun h (⟨t,ht⟩ : F)
    exact ⟨decide_eq_decide.mp (congrArg Prod.fst he),decide_eq_decide.mp (congrArg Prod.snd he)⟩
  · intro hp
    funext t
    apply Prod.ext
    · exact decide_eq_decide.mpr (hp t.val t.property).1
    · exact decide_eq_decide.mpr (hp t.val t.property).2

theorem pattern_not_mem {F : Finset α} {x y : α} (hp : FiniteOrder.Pattern F x y) (hx : x ∉ F) : y ∉ F := by
  intro hy
  rcases lt_trichotomy x y with hxy | he | hyx
  · exact (lt_irrefl y) ((hp y hy).1.mp hxy)
  · exact hx (he.symm ▸ hy)
  · exact (lt_irrefl y) ((hp y hy).2.mp hyx)

theorem same_cell {F : Finset α} {c : Code F} {x y : α}
    (hx : x ∈ cell F c) (hp : FiniteOrder.Pattern F x y) : y ∈ cell F c :=
  ⟨pattern_not_mem hp hx.1,((code_eq_iff F x y).mpr hp).symm.trans hx.2⟩

theorem connected (F : Finset α) (c : Code F) : OrdConnected (cell F c) := by
  constructor
  intro x hx y hy z hz
  have hp : FiniteOrder.Pattern F x y := (code_eq_iff F x y).mp (hx.2.trans hy.2.symm)
  exact same_cell hx (hp.between hz.1 hz.2)

theorem disjoint (F : Finset α) (c d : Code F) (hcd : c ≠ d) : Disjoint (cell F c) (cell F d) := by
  apply Set.disjoint_left.mpr
  intro x hx hd
  exact hcd (hx.2.symm.trans hd.2)

theorem controlled {F : Finset α} {D : Set α} (hF : FiniteOrder.Controls F D)
    (c : Code F) (x : α) (hx : x ∈ cell F c) (hxD : x ∈ D) : cell F c ⊆ D := by
  intro y hy
  exact (hF x y ((code_eq_iff F x y).mp (hx.2.trans hy.2.symm))).mp hxD

variable [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α]

theorem no_endpoints (F : Finset α) (c : Code F) (x : α) (hx : x ∈ cell F c) :
    (∃ y ∈ cell F c, y < x) ∧ (∃ y ∈ cell F c, x < y) := by
  obtain ⟨l,u,hlx,hxu,hGap⟩ := FiniteOrder.finite_gap F x hx.1
  have hAvoid : ∀ t ∈ Set.Ioo l u, t ∉ F := by
    intro t ht htF
    rcases hGap t htF with htl | hut
    · exact (not_lt_of_ge htl) ht.1
    · exact (not_lt_of_ge hut) ht.2
  have hxI : x ∈ Set.Ioo l u := ⟨hlx,hxu⟩
  obtain ⟨y,hly,hyx⟩ := exists_between hlx
  obtain ⟨z,hxz,hzu⟩ := exists_between hxu
  exact ⟨⟨y,same_cell hx (FiniteOrderIntervalPatterns.same_pattern F l u hAvoid hxI ⟨hly,hyx.trans hxu⟩),hyx⟩,
    ⟨z,same_cell hx (FiniteOrderIntervalPatterns.same_pattern F l u hAvoid hxI ⟨hlx.trans hxz,hzu⟩),hxz⟩⟩

end IntegrationInACVF.Section3ACVF.FiniteOrderCells
