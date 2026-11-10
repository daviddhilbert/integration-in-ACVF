module

public import IntegrationSection3.InfiniteCosets
public import Mathlib.Tactic.Ring

@[expose] public section

/-! A closed cut of an open ball with infinitely many smaller quotient
classes on each side. This is pure valuation geometry; actual coding and
first-order definability are supplied separately. -/

open Set

namespace IntegrationInACVF.Section3.RelativeQuotientCut

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem closed_saturated (v : Valuation K Γ) (H : AddSubgroup K)
    (u : K) (hH : ∀ x, x ∈ H ↔ v x < v u)
    (c t : K) (hut : v u < v t) {x y : K}
    (he : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) :
    v (x-c) ≤ v t ↔ v (y-c) ≤ v t := by
  have hxy : v (x-y) < v t :=
    ((hH _).mp (QuotientAddGroup.eq_iff_sub_mem.mp he)).trans hut
  have hyx : v (y-x) < v t := by rwa [v.map_sub_swap]
  constructor
  · intro hx
    have hsum : y-c = (y-x)+(x-c) := by ring
    rw [hsum]
    exact (v.map_add _ _).trans (max_le hyx.le hx)
  · intro hy
    have hsum : x-c = (x-y)+(y-c) := by ring
    rw [hsum]
    exact (v.map_add _ _).trans (max_le hxy.le hy)

theorem exists_cut (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t, v r < v t ∧ v t < v s)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (u : K) (hH : ∀ x, x ∈ H ↔ v x < v u)
    (c s : K) (hus : v u < v s) :
    ∃ t : K, v u < v t ∧ v t < v s ∧
      ({x | v (x-c) ≤ v t} ⊆ {x | v (x-c) < v s}) ∧
      (QuotientAddGroup.mk' H '' {x | v (x-c) ≤ v t}).Infinite ∧
      (QuotientAddGroup.mk' H ''
        ({x | v (x-c) < v s} \ {x | v (x-c) ≤ v t})).Infinite ∧
      (∀ x y, QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y →
        (v (x-c) ≤ v t ↔ v (y-c) ≤ v t)) := by
  obtain ⟨t,hut,hts⟩ := hdense u s hus
  obtain ⟨z,htz,hzs⟩ := hdense t s hts
  have hin := InfiniteCosets.infinite_cosets_in_open_ball v hunit H u hH c (v t) hut
  have hout := InfiniteCosets.infinite_cosets_in_open_ball v hunit H u hH (c+z) (v t) hut
  refine ⟨t,hut,hts,(fun _ hx => hx.trans_lt hts),?_,?_,?_⟩
  · exact hin.mono (Set.image_mono fun _ hx => hx.le)
  · apply hout.mono
    apply Set.image_mono
    intro x hx
    have he : x-c = (x-(c+z))+z := by ring
    have hval : v (x-c) = v z := by
      rw [he]
      exact v.map_add_eq_of_lt_right (hx.trans htz)
    exact ⟨by change v (x-c) < v s; rwa [hval],
      by change ¬ v (x-c) ≤ v t; rw [hval]; exact not_le_of_gt htz⟩
  · exact fun x y he => closed_saturated v H u hH c t hut he

end IntegrationInACVF.Section3.RelativeQuotientCut
