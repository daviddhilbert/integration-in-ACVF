module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.Ring
public import IntegrationSection3.AffineHoleCosets

@[expose] public section

/-! Summing increments with strictly small errors keeps the error strictly
small. This is the valuation estimate for RV equivariance under integers. -/

namespace IntegrationInACVF.Section3.ValuationProgressions

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem error_lt (v : Valuation K Γ) (a : ℕ → K) (b : K) (hb : b ≠ 0)
    (hstep : ∀ n, v (a (n+1) - a n - b) < v b) (n : ℕ) :
    v (a n - a 0 - (n : K) * b) < v b := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,sub_self,sub_zero,map_zero] using
      (pos_iff_ne_zero.mpr ((v.ne_zero_iff).mpr hb))
  | succ n ih =>
    have he : a (n+1) - a 0 - ((n+1 : ℕ) : K) * b =
        (a n - a 0 - (n : K) * b) + (a (n+1) - a n - b) := by
      rw [Nat.cast_add,Nat.cast_one]
      ring
    rw [he]
    exact v.map_add_lt ih (hstep n)

theorem affine_mem_open (v : Valuation K Γ)
    (hunit : ∀ n : ℕ, n ≠ 0 → v (n : K) = 1)
    (c a b : K) (R : Γ) (ha : v (a-c) < R) (hb : v (b-c) < R) (n : ℕ) :
    v (AffineHoleCosets.affine a b n-c) < R := by
  have hba : v (b-a) < R := by
    have he : b-a = (b-c)-(a-c) := by ring
    rw [he]
    exact v.map_sub_lt hb ha
  by_cases hn : n = 0
  · simpa only [AffineHoleCosets.affine,hn,Nat.cast_zero,zero_mul,add_zero] using ha
  · have he : AffineHoleCosets.affine a b n-c = (a-c) + (n : K) * (b-a) := by
      unfold AffineHoleCosets.affine
      ring
    rw [he]
    exact v.map_add_lt ha (by rwa [map_mul,hunit n hn,one_mul])

end IntegrationInACVF.Section3.ValuationProgressions
