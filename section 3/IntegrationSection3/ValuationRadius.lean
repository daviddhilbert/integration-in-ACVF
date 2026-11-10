module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Radius comparisons for actual values of a multiplicative valuation.
Open-to-closed comparison displays its density hypothesis explicitly; the
actual ACVF bridge supplies it from the pinned formalized geometry. -/

namespace IntegrationInACVF.Section3.ValuationRadius

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem closed_radius_le_of_subset (v : Valuation K Γ) (a b r s : K)
    (hsub : {x | v (x-a) ≤ v r} ⊆ {x | v (x-b) ≤ v s}) : v r ≤ v s := by
  by_contra hn
  have hsr : v s < v r := lt_of_not_ge hn
  have ha : v (a-a) ≤ v r := by simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v r)
  have hab : v (a-b) ≤ v s := hsub ha
  have hba : v (b-a) ≤ v s := by rwa [v.map_sub_swap]
  have hx : v ((b+r)-a) ≤ v r := by
    have he : (b+r)-a = (b-a)+r := by ring
    rw [he]
    exact (v.map_add _ _).trans (max_le (hba.trans hsr.le) le_rfl)
  have hbad : v ((b+r)-b) ≤ v s := hsub hx
  have he : (b+r)-b = r := by ring
  rw [he] at hbad
  exact not_le_of_gt hsr hbad

theorem closed_radius_lt_of_subset_open (v : Valuation K Γ) (a b r s : K)
    (hsub : {x | v (x-a) ≤ v r} ⊆ {x | v (x-b) < v s}) : v r < v s := by
  by_contra hn
  have hsr : v s ≤ v r := le_of_not_gt hn
  have ha : v (a-a) ≤ v r := by simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v r)
  have hab : v (a-b) < v s := hsub ha
  have hba : v (b-a) < v s := by rwa [v.map_sub_swap]
  have hx : v ((b+s)-a) ≤ v r := by
    have he : (b+s)-a = (b-a)+s := by ring
    rw [he]
    exact (v.map_add _ _).trans (max_le (hba.le.trans hsr) hsr)
  have hbad : v ((b+s)-b) < v s := hsub hx
  have he : (b+s)-b = s := by ring
  rw [he] at hbad
  exact lt_irrefl _ hbad

theorem open_radius_le_of_subset_closed (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (a b r s : K) (hr : r ≠ 0)
    (hsub : {x | v (x-a) < v r} ⊆ {x | v (x-b) ≤ v s}) : v r ≤ v s := by
  by_contra hn
  have hsr : v s < v r := lt_of_not_ge hn
  have ha : v (a-a) < v r := by
    simpa only [sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr))
  have hab : v (a-b) ≤ v s := hsub ha
  have hba : v (b-a) ≤ v s := by rwa [v.map_sub_swap]
  obtain ⟨t,hst,htr⟩ := hdense s r hsr
  have hx : v ((b+t)-a) < v r := by
    have he : (b+t)-a = (b-a)+t := by ring
    rw [he]
    exact (v.map_add _ _).trans_lt (max_lt (hba.trans_lt hsr) htr)
  have hbad : v ((b+t)-b) ≤ v s := hsub hx
  have he : (b+t)-b = t := by ring
  rw [he] at hbad
  exact not_le_of_gt hst hbad

theorem open_ne_closed (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (a b r s : K) (hr : r ≠ 0) :
    {x | v (x-a) < v r} ≠ {x | v (x-b) ≤ v s} := by
  intro he
  have hle := open_radius_le_of_subset_closed v hdense a b r s hr he.subset
  have hlt := closed_radius_lt_of_subset_open v b a s r he.symm.subset
  exact not_lt_of_ge hle hlt

end IntegrationInACVF.Section3.ValuationRadius
