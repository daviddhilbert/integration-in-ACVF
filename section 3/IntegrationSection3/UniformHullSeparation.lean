module

public import IntegrationSection3.RelativeQuotientCut
public import IntegrationSection3.QuotientCover

@[expose] public section

/-! Uniformly small closed hulls cannot cover an open ball in a family
whose closed-ball intersection traces are always finite or cofinite. -/

open Set

namespace IntegrationInACVF.Section3.UniformHullSeparation

variable {K Γ J : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem impossible (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t, v r < v t ∧ v t < v s)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (c s r : K) (hrs : v r < v s) (T : Set J) (C : J → Set K)
    (hsub : ∀ j ∈ T, C j ⊆ {x | v (x-c) < v s})
    (hcover : ∀ x, v (x-c) < v s → ∃ j ∈ T, x ∈ C j)
    (hhull : ∀ j ∈ T, ∃ a : K, C j ⊆ {x | v (x-a) ≤ v r})
    (htrace : ∀ t : K, v t < v s →
      (QuotientCover.meets T C {x | v (x-c) ≤ v t}).Finite ∨
        (T \ QuotientCover.meets T C {x | v (x-c) ≤ v t}).Finite) : False := by
  obtain ⟨u,hru,hus⟩ := hdense r s hrs
  have hu0 : v u ≠ 0 := ne_of_gt ((zero_le : (0 : Γ) ≤ v r).trans_lt hru)
  let H := v.ltAddSubgroup (Units.mk0 (v u) hu0)
  have hH (x : K) : x ∈ H ↔ v x < v u := Iff.rfl
  have hspan (j : J) (hj : j ∈ T) (x : K) (hx : x ∈ C j) (y : K) (hy : y ∈ C j) :
      QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y := by
    obtain ⟨a,ha⟩ := hhull j hj
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply (hH _).mpr
    have he : x-y = (x-a)-(y-a) := by ring
    rw [he]
    exact (v.map_sub _ _).trans_lt (max_lt ((ha hx).trans_lt hru) ((ha hy).trans_lt hru))
  obtain ⟨t,hut,hts,hDP,hD,hcomp,hsat⟩ :=
    RelativeQuotientCut.exists_cut v hdense hunit H u hH c s hus
  have hleft := QuotientCover.meets_infinite (QuotientAddGroup.mk' H) hDP hD C hspan hcover
  have hright := QuotientCover.complement_infinite (QuotientAddGroup.mk' H) hcomp C hsub hspan
    (fun x _ y _ he => hsat x y he) hcover
  exact (htrace t hts).elim hleft hright

end IntegrationInACVF.Section3.UniformHullSeparation
