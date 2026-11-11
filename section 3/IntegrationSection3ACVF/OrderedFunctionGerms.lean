import IntegrationSection3ACVF.FiniteOrderGerms
import IntegrationSection3ACVF.OrderedGermMonotonicity
import IntegrationSection3ACVF.OrderedLocalExtrema

/-! Injective functions have two strict one-sided signs at interior
points whenever their comparison cuts have actual finite controllers.
The two mixed signs are exactly strict local minima or maxima. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.OrderedFunctionGerms

variable {α β : Type*} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
  [DenselyOrdered α] [LinearOrder β]

def rightAbove (D : Set α) (f : α → β) (x : α) : Prop :=
  ∃ u, x < u ∧ ∀ y ∈ D, x < y → y < u → f x < f y

def leftBelow (D : Set α) (f : α → β) (x : α) : Prop :=
  ∃ l, l < x ∧ ∀ y ∈ D, l < y → y < x → f y < f x

theorem right_sign (D : Set α) (f : α → β) (hInj : Set.InjOn f D) (x : α) (hxD : x ∈ D)
    (hInterior : ∃ v, x < v ∧ Set.Ioo x v ⊆ D)
    (hControl : ∃ F, FiniteOrder.Controls F {y | y ∈ D ∧ f x < f y}) :
    rightAbove D f x ∨ rightAbove (β := OrderDual β) D f x := by
  obtain ⟨v,hxv,hvD⟩ := hInterior
  obtain ⟨u,hxu,hConst⟩ := FiniteOrderGerms.right_constant hControl x
  obtain ⟨z,hxz,hz⟩ := exists_between (lt_min hxv hxu)
  have hzv : z < v := hz.trans_le (min_le_left _ _)
  have hzu : z < u := hz.trans_le (min_le_right _ _)
  have hzD : z ∈ D := hvD ⟨hxz,hzv⟩
  by_cases hUp : f x < f z
  · refine Or.inl ⟨u,hxu,?_⟩
    intro y hyD hxy hyu
    exact ((hConst z y hxz hzu hxy hyu).mp ⟨hzD,hUp⟩).2
  · refine Or.inr ⟨u,hxu,?_⟩
    intro y hyD hxy hyu
    have hn : ¬ f x < f y := fun h => hUp ((hConst y z hxy hyu hxz hzu).mp ⟨hyD,h⟩).2
    exact lt_of_le_of_ne (le_of_not_gt hn) (fun he => hxy.ne (hInj hxD hyD he))

theorem left_sign (D : Set α) (f : α → β) (hInj : Set.InjOn f D) (x : α) (hxD : x ∈ D)
    (hInterior : ∃ l, l < x ∧ Set.Ioo l x ⊆ D)
    (hControl : ∃ F, FiniteOrder.Controls F {y | y ∈ D ∧ f x < f y}) :
    leftBelow D f x ∨ leftBelow (β := OrderDual β) D f x := by
  obtain ⟨l,hlx,hlD⟩ := hInterior
  obtain ⟨v,hvx,hConst⟩ := FiniteOrderGerms.left_constant hControl x
  obtain ⟨z,hz,hzx⟩ := exists_between (max_lt hlx hvx)
  have hlz : l < z := (le_max_left _ _).trans_lt hz
  have hvz : v < z := (le_max_right _ _).trans_lt hz
  have hzD : z ∈ D := hlD ⟨hlz,hzx⟩
  by_cases hUp : f x < f z
  · refine Or.inr ⟨v,hvx,?_⟩
    intro y hyD hvy hyx
    exact ((hConst z y hvz hzx hvy hyx).mp ⟨hzD,hUp⟩).2
  · refine Or.inl ⟨v,hvx,?_⟩
    intro y hyD hvy hyx
    have hn : ¬ f x < f y := fun h => hUp ((hConst y z hvy hyx hvz hzx).mp ⟨hyD,h⟩).2
    exact lt_of_le_of_ne (le_of_not_gt hn) (fun he => hyx.ne (hInj hyD hxD he))

theorem classify (D : Set α) (f : α → β) (hInj : Set.InjOn f D) (x : α) (hxD : x ∈ D)
    (hInterior : ∃ l u, l < x ∧ x < u ∧ Set.Ioo l u ⊆ D)
    (hControl : ∃ F, FiniteOrder.Controls F {y | y ∈ D ∧ f x < f y}) :
    OrderedGermMonotonicity.increasing D f x ∨
    OrderedGermMonotonicity.increasing (β := OrderDual β) D f x ∨
    (x ∈ {x | x ∈ D ∧ ∃ l u, l < x ∧ x < u ∧
      ∀ y ∈ D, l < y → y < u → y ≠ x → f x < f y}) ∨
    (x ∈ {x | x ∈ D ∧ ∃ l u, l < x ∧ x < u ∧
      ∀ y ∈ D, l < y → y < u → y ≠ x → f y < f x}) := by
  obtain ⟨l,u,hlx,hxu,hD⟩ := hInterior
  have hL := left_sign D f hInj x hxD ⟨l,hlx,fun y hy => hD ⟨hy.1,hy.2.trans hxu⟩⟩ hControl
  have hR := right_sign D f hInj x hxD ⟨u,hxu,fun y hy => hD ⟨hlx.trans hy.1,hy.2⟩⟩ hControl
  rcases hL with hL | hL <;> rcases hR with hR | hR
  · exact Or.inl ⟨hL,hR⟩
  · obtain ⟨l,hl,hLeft⟩ := hL
    obtain ⟨u,hu,hRight⟩ := hR
    refine Or.inr (Or.inr (Or.inr ⟨hxD,l,u,hl,hu,?_⟩))
    intro y hy hly hyu hne
    rcases lt_or_gt_of_ne hne with hyx | hxy
    · exact hLeft y hy hly hyx
    · exact hRight y hy hxy hyu
  · obtain ⟨l,hl,hLeft⟩ := hL
    obtain ⟨u,hu,hRight⟩ := hR
    refine Or.inr (Or.inr (Or.inl ⟨hxD,l,u,hl,hu,?_⟩))
    intro y hy hly hyu hne
    rcases lt_or_gt_of_ne hne with hyx | hxy
    · exact hLeft y hy hly hyx
    · exact hRight y hy hxy hyu
  · exact Or.inr (Or.inl ⟨hL,hR⟩)

end IntegrationInACVF.Section3ACVF.OrderedFunctionGerms
