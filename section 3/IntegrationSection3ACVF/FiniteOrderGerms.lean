import IntegrationSection3ACVF.FiniteOrderBounds

/-! One-sided constant germs from a genuine finite order controller.
The centre itself may be one of the finitely many endpoints. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderGerms

variable {α : Type*} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]

theorem right_constant {D : Set α} (hControl : ∃ F, FiniteOrder.Controls F D) (x : α) :
    ∃ u, x < u ∧ ∀ y z, x < y → y < u → x < z → z < u → (y ∈ D ↔ z ∈ D) := by
  classical
  obtain ⟨F,hF⟩ := hControl
  obtain ⟨l,u,hl,hu,hGap⟩ := FiniteOrder.finite_gap (F.erase x) x
    (fun h => (Finset.mem_erase.mp h).1 rfl)
  refine ⟨u,hu,?_⟩
  intro y z hxy hyu hxz hzu
  apply hF y z
  intro t ht
  by_cases htx : t = x
  · subst t
    exact ⟨iff_of_false (not_lt_of_ge hxy.le) (not_lt_of_ge hxz.le),iff_of_true hxy hxz⟩
  · rcases hGap t (Finset.mem_erase.mpr ⟨htx,ht⟩) with htl | hut
    · have hty : t < y := htl.trans_lt (hl.trans hxy)
      have htz : t < z := htl.trans_lt (hl.trans hxz)
      exact ⟨iff_of_false (not_lt_of_ge hty.le) (not_lt_of_ge htz.le),iff_of_true hty htz⟩
    · have hyt : y < t := hyu.trans_le hut
      have hzt : z < t := hzu.trans_le hut
      exact ⟨iff_of_true hyt hzt,iff_of_false (not_lt_of_ge hyt.le) (not_lt_of_ge hzt.le)⟩

theorem left_constant {D : Set α} (hControl : ∃ F, FiniteOrder.Controls F D) (x : α) :
    ∃ l, l < x ∧ ∀ y z, l < y → y < x → l < z → z < x → (y ∈ D ↔ z ∈ D) := by
  obtain ⟨F,hF⟩ := hControl
  have hDual : @FiniteOrder.Controls (OrderDual α) inferInstance F D :=
    fun y z hp => hF y z (fun t ht => ⟨(hp t ht).2,(hp t ht).1⟩)
  obtain ⟨l,hl,hLoc⟩ := right_constant (α := OrderDual α) ⟨F,hDual⟩ x
  exact ⟨l,hl,fun y z hly hyx hlz hzx => hLoc y z hyx hly hzx hlz⟩

end IntegrationInACVF.Section3ACVF.FiniteOrderGerms
