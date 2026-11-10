module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Infinitely many small open-ball cosets inside a larger open ball.
The valuation-unit condition on nonzero natural numbers is precisely the
residue-characteristic-zero input, to be supplied by the actual ACVF model. -/

open Set

namespace IntegrationInACVF.Section3.InfiniteCosets

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem map_nat_difference (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (n m : ℕ) (hne : n ≠ m) : v ((n : K) - (m : K)) = 1 := by
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · rw [v.map_sub_swap,← Nat.cast_sub (Nat.le_of_lt hnm)]
    exact hunit (m-n) (Nat.ne_of_gt (Nat.sub_pos_of_lt hnm))
  · rw [← Nat.cast_sub (Nat.le_of_lt hmn)]
    exact hunit (n-m) (Nat.ne_of_gt (Nat.sub_pos_of_lt hmn))

/-- Integer translates of a point by an element on the small ball's boundary
are in distinct small-ball cosets and stay inside the larger open ball. -/
theorem infinite_cosets_in_open_ball (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (H : AddSubgroup K) (u : K) (hH : ∀ x : K, x ∈ H ↔ v x < v u)
    (a : K) (R : Γ) (huR : v u < R) :
    (QuotientAddGroup.mk' H '' {x : K | v (x-a) < R}).Infinite := by
  let f : ℕ → K ⧸ H := fun n => QuotientAddGroup.mk' H (a + (n : K) * u)
  have hinj : Function.Injective f := by
    intro n m he
    by_contra hne
    have hd : (a + (n : K) * u) - (a + (m : K) * u) ∈ H :=
      QuotientAddGroup.eq_iff_sub_mem.mp he
    have hlt := (hH _).mp hd
    have heq : (a + (n : K) * u) - (a + (m : K) * u) =
        ((n : K) - (m : K)) * u := by ring
    rw [heq,map_mul,map_nat_difference v hunit n m hne,one_mul] at hlt
    exact lt_irrefl _ hlt
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n,rfl⟩
  refine ⟨a + (n : K) * u,?_,rfl⟩
  change v ((a + (n : K) * u) - a) < R
  rw [add_sub_cancel_left,map_mul]
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero, map_zero,zero_mul] using (show (0 : Γ) ≤ v u from zero_le).trans_lt huR
  · rw [hunit n hn,one_mul]
    exact huR

end IntegrationInACVF.Section3.InfiniteCosets
