import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-! Finite support arithmetic used for the RV weight condition in Lemma 6.3. -/

open scoped BigOperators

namespace IntegrationInACVF.Section6

/-- Multiplying one nonzero coordinate by the new blowup parameter removes
one from the support exactly at parameter zero. No order on RV is used. -/
theorem support_scale_balance {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [CommGroupWithZero G] [DecidableEq G] (i : ι) (t : ι → G) (s : G) (ht : t i ≠ 0) :
    (∑ j, if (if j = i then s * t j else t j) ≠ 0 then 1 else 0) +
      (if s = 0 then 1 else 0) = ∑ j, if t j ≠ 0 then 1 else 0 := by
  have hsum : (∑ j ∈ (Finset.univ : Finset ι).erase i,
      if (if j = i then s * t j else t j) ≠ 0 then 1 else 0) =
      ∑ j ∈ (Finset.univ : Finset ι).erase i, if t j ≠ 0 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [hsum]
  by_cases hs : s = 0
  · simp [hs, ht]
  · simp [hs, mul_ne_zero hs ht, ht]

end IntegrationInACVF.Section6
