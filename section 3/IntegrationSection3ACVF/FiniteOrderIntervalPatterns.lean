import IntegrationSection3ACVF.FiniteOrderBounds

/-! Every two points of an endpoint-free open interval have the same
pattern against the original finite endpoint set. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderIntervalPatterns

variable {α : Type*} [LinearOrder α]

theorem same_pattern (F : Finset α) (l u : α)
    (hAvoid : ∀ t ∈ Set.Ioo l u, t ∉ F) {x y : α}
    (hx : x ∈ Set.Ioo l u) (hy : y ∈ Set.Ioo l u) : FiniteOrder.Pattern F x y := by
  intro t ht
  by_cases htl : t ≤ l
  · have htx : t < x := htl.trans_lt hx.1
    have hty : t < y := htl.trans_lt hy.1
    exact ⟨iff_of_false (not_lt_of_ge htx.le) (not_lt_of_ge hty.le),iff_of_true htx hty⟩
  · have hut : u ≤ t := by
      by_contra htu
      exact hAvoid t ⟨lt_of_not_ge htl,lt_of_not_ge htu⟩ ht
    have hxt : x < t := hx.2.trans_le hut
    have hyt : y < t := hy.2.trans_le hut
    exact ⟨iff_of_true hxt hyt,iff_of_false (not_lt_of_ge hxt.le) (not_lt_of_ge hyt.le)⟩

end IntegrationInACVF.Section3ACVF.FiniteOrderIntervalPatterns
