import Mathlib.Order.Interval.Set.OrdConnected

/-! Local strict monotonicity on bounded open subintervals fixes a
single orientation on an entire open order cell, including rays. -/

open Set Classical

namespace IntegrationInACVF.Section3ACVF.OrderedCellMonotonicity

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem mono_or_anti (C : Set α) (f : α → β) (hC : C.Nonempty) (hConn : OrdConnected C)
    (hNoMin : ∀ x ∈ C, ∃ y ∈ C, y < x) (hNoMax : ∀ x ∈ C, ∃ y ∈ C, x < y)
    (hLocal : ∀ l u, l < u → Set.Ioo l u ⊆ C →
      StrictMonoOn f (Set.Ioo l u) ∨ StrictAntiOn f (Set.Ioo l u)) :
    StrictMonoOn f C ∨ StrictAntiOn f C := by
  obtain ⟨p,hp⟩ := hC
  obtain ⟨q,hq,hpq⟩ := hNoMax p hp
  have hWindow (x : α) (hx : x ∈ C) (y : α) (hy : y ∈ C) :
      ∃ l u, l < x ∧ l < p ∧ y < u ∧ q < u ∧ Set.Ioo l u ⊆ C := by
    have hMin : min x p ∈ C := by
      rcases le_total x p with h | h
      · simpa only [min_eq_left h] using hx
      · simpa only [min_eq_right h] using hp
    have hMax : max y q ∈ C := by
      rcases le_total y q with h | h
      · simpa only [max_eq_right h] using hq
      · simpa only [max_eq_left h] using hy
    obtain ⟨l,hl,hlMin⟩ := hNoMin _ hMin
    obtain ⟨u,hu,hMaxU⟩ := hNoMax _ hMax
    exact ⟨l,u,hlMin.trans_le (min_le_left _ _),hlMin.trans_le (min_le_right _ _),
      (le_max_left _ _).trans_lt hMaxU,(le_max_right _ _).trans_lt hMaxU,
      fun _ hz => hConn.out hl hu ⟨hz.1.le,hz.2.le⟩⟩
  by_cases hUp : f p < f q
  · refine Or.inl ?_
    intro x hx y hy hxy
    obtain ⟨l,u,hlx,hlp,hyu,hqu,hSub⟩ := hWindow x hx y hy
    rcases hLocal l u (hlx.trans (hxy.trans hyu)) hSub with h | h
    · exact h ⟨hlx,hxy.trans hyu⟩ ⟨hlx.trans hxy,hyu⟩ hxy
    · exact ((not_lt_of_gt hUp) (h ⟨hlp,hpq.trans hqu⟩ ⟨hlp.trans hpq,hqu⟩ hpq)).elim
  · refine Or.inr ?_
    intro x hx y hy hxy
    obtain ⟨l,u,hlx,hlp,hyu,hqu,hSub⟩ := hWindow x hx y hy
    rcases hLocal l u (hlx.trans (hxy.trans hyu)) hSub with h | h
    · exact (hUp (h ⟨hlp,hpq.trans hqu⟩ ⟨hlp.trans hpq,hqu⟩ hpq)).elim
    · exact h ⟨hlx,hxy.trans hyu⟩ ⟨hlx.trans hxy,hyu⟩ hxy

end IntegrationInACVF.Section3ACVF.OrderedCellMonotonicity
