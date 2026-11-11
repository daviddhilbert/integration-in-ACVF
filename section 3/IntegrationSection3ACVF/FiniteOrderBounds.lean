import Section4.CanonicalOrderController
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic


/-! Definable completeness from an actual finite endpoint controller.
No completeness or Archimedean assumption on the dense order is used. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderBounds

variable {α : Type*} [LinearOrder α] [NoMaxOrder α] [DenselyOrdered α]

theorem exists_isLUB {D : Set α} (hne : D.Nonempty) (hBound : BddAbove D)
    (hControl : ∃ F, FiniteOrder.Controls F D) : ∃ r, IsLUB D r := by
  classical
  obtain ⟨F,hF⟩ := hControl
  obtain ⟨b,hb⟩ := hBound
  have hNoTail (x : α) (hx : x ∈ D) : ¬ ∀ t ∈ F, t < x := by
    intro hTail
    obtain ⟨y,hy⟩ := exists_gt (max x b)
    have hxy : x < y := lt_of_le_of_lt (le_max_left _ _) hy
    have hyD : y ∈ D := (hF x y (fun t ht =>
      ⟨iff_of_false (not_lt_of_ge (hTail t ht).le) (not_lt_of_ge ((hTail t ht).trans hxy).le),
       iff_of_true (hTail t ht) ((hTail t ht).trans hxy)⟩)).mp hx
    exact (not_lt_of_ge (hb hyD)) (lt_of_le_of_lt (le_max_right _ _) hy)
  have hFn : F.Nonempty := by
    by_contra he
    obtain ⟨x,hx⟩ := hne
    exact hNoTail x hx (fun t ht => (he ⟨t,ht⟩).elim)
  let G := F.filter (fun t => t ∈ upperBounds D)
  have hGn : G.Nonempty := by
    refine ⟨F.max' hFn,Finset.mem_filter.mpr ⟨F.max'_mem hFn,?_⟩⟩
    intro x hx
    by_contra hn
    exact hNoTail x hx (fun t ht => lt_of_le_of_lt (F.le_max' t ht) (lt_of_not_ge hn))
  let r := G.min' hGn
  have hrG : r ∈ G := G.min'_mem hGn
  have hrUpper : r ∈ upperBounds D := (Finset.mem_filter.mp hrG).2
  refine ⟨r,hrUpper,?_⟩
  intro c hc
  by_contra hrc
  have hcr : c < r := lt_of_not_ge hrc
  let L := F.filter (· < r)
  have hAbove : ∃ x ∈ D, ∀ t ∈ F, t < r → t < x := by
    by_cases hLn : L.Nonempty
    · let l := L.max' hLn
      have hlF : l ∈ F := (Finset.mem_filter.mp (L.max'_mem hLn)).1
      have hlr : l < r := (Finset.mem_filter.mp (L.max'_mem hLn)).2
      have hlNot : l ∉ upperBounds D := by
        intro hlU
        have hlG : l ∈ G := Finset.mem_filter.mpr ⟨hlF,hlU⟩
        exact (not_lt_of_ge (G.min'_le l hlG)) hlr
      obtain ⟨x,hx,hxl⟩ : ∃ x ∈ D, l < x := by
        simpa only [upperBounds,Set.mem_ofPred_eq,not_forall,not_le,exists_prop] using hlNot
      exact ⟨x,hx,fun t ht htr => lt_of_le_of_lt (L.le_max' t (Finset.mem_filter.mpr ⟨ht,htr⟩)) hxl⟩
    · obtain ⟨x,hx⟩ := hne
      exact ⟨x,hx,fun t ht htr => (hLn ⟨t,Finset.mem_filter.mpr ⟨ht,htr⟩⟩).elim⟩
  obtain ⟨x,hx,hPast⟩ := hAbove
  have hxr : x < r := lt_of_le_of_lt (hc hx) hcr
  obtain ⟨y,hyL,hyR⟩ := exists_between (max_lt hcr hxr)
  have hp : FiniteOrder.Pattern F x y := by
    intro t ht
    by_cases htr : t < r
    · have htx : t < x := hPast t ht htr
      have hty : t < y := htx.trans (lt_of_le_of_lt (le_max_right _ _) hyL)
      exact ⟨iff_of_false (not_lt_of_ge htx.le) (not_lt_of_ge hty.le),iff_of_true htx hty⟩
    · have hrt : r ≤ t := le_of_not_gt htr
      have hxt := hxr.trans_le hrt
      have hyt := hyR.trans_le hrt
      exact ⟨iff_of_true hxt hyt,iff_of_false (not_lt_of_ge hxt.le) (not_lt_of_ge hyt.le)⟩
  exact (not_lt_of_ge (hc ((hF x y hp).mp hx))) (lt_of_le_of_lt (le_max_left _ _) hyL)

variable [NoMinOrder α]

theorem exists_isGLB {D : Set α} (hne : D.Nonempty) (hBound : BddBelow D)
    (hControl : ∃ F, FiniteOrder.Controls F D) : ∃ r, IsGLB D r := by
  obtain ⟨F,hF⟩ := hControl
  have hDual : @FiniteOrder.Controls (OrderDual α) inferInstance F D := by
    intro x y hp
    exact hF x y (fun t ht => ⟨(hp t ht).2,(hp t ht).1⟩)
  exact exists_isLUB (α := OrderDual α) hne hBound ⟨F,hDual⟩

theorem finite_or_contains_interval {D : Set α} (hControl : ∃ F, FiniteOrder.Controls F D) :
    D.Finite ∨ ∃ l u, l < u ∧ Set.Ioo l u ⊆ D := by
  classical
  obtain ⟨F,hF⟩ := hControl
  by_cases hD : D.Finite
  · exact Or.inl hD
  have hn : ¬ ∀ x, x ∈ D → x ∈ F := fun h => hD (F.finite_toSet.subset h)
  obtain ⟨x,hx⟩ := not_forall.mp hn
  obtain ⟨hxD,hxF⟩ := not_imp.mp hx
  obtain ⟨l,u,hlx,hxu,hLoc⟩ := FiniteOrder.local_constant_of_missing hF hxF
  exact Or.inr ⟨l,u,hlx.trans hxu,fun z hz => (hLoc z hz.1 hz.2).mpr hxD⟩

theorem exists_isLeast_of_closed_upper {D : Set α} (hne : D.Nonempty)
    (hBound : BddBelow D) (hControl : ∃ F, FiniteOrder.Controls F D)
    (hUpper : ∀ x ∈ D, ∀ y, x ≤ y → y ∈ D)
    (hClosed : ∀ r, (∀ t, r < t → t ∈ D) → r ∈ D) : ∃ r, IsLeast D r := by
  obtain ⟨r,hr⟩ := exists_isGLB hne hBound hControl
  refine ⟨r,hClosed r ?_,hr.1⟩
  intro t hrt
  have ht : t ∉ lowerBounds D := fun ht => (not_lt_of_ge (hr.2 ht)) hrt
  have hn : ¬ ∀ x, x ∈ D → t ≤ x := ht
  obtain ⟨x,hx⟩ := not_forall.mp hn
  obtain ⟨hxD,htx⟩ := not_imp.mp hx
  exact hUpper x hxD t (le_of_lt (lt_of_not_ge htx))

end IntegrationInACVF.Section3ACVF.FiniteOrderBounds
