import IntegrationSection3ACVF.FiniteOrderCells
import IntegrationSection3ACVF.OrderedCellMonotonicity
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Finite nonempty open-cell indices and coverage of a controlled set.
This is a genuine finite endpoint partition, with no chosen sample points. -/

open Set Classical
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteOrderCellPartition

open FiniteOrderCells

variable {α β : Type*} [LinearOrder α]

def Index (F : Finset α) (D : Set α) := {c : Code F | (cell F c).Nonempty ∧ cell F c ⊆ D}

instance finite_index (F : Finset α) (D : Set α) : Finite (Index F D) := by
  unfold Index
  infer_instance

theorem controls_mono {F G : Finset α} {D : Set α} (hFG : F ⊆ G)
    (hF : FiniteOrder.Controls F D) : FiniteOrder.Controls G D :=
  fun x y hp => hF x y (fun t ht => hp t (hFG ht))

theorem controls_Icc (F : Finset α) (a b : α) (ha : a ∈ F) (hb : b ∈ F) :
    FiniteOrder.Controls F (Set.Icc a b) := by
  intro x y hp
  change (a ≤ x ∧ x ≤ b) ↔ (a ≤ y ∧ y ≤ b)
  simpa only [not_lt] using (not_congr (hp a ha).1).and (not_congr (hp b hb).2)

theorem point_or_cell {F : Finset α} {D : Set α} (hF : FiniteOrder.Controls F D)
    (x : α) (hxD : x ∈ D) : x ∈ F ∨ ∃ c : Index F D, x ∈ cell F c.val := by
  by_cases hx : x ∈ F
  · exact Or.inl hx
  · have hxC : x ∈ cell F (code F x) := ⟨hx,rfl⟩
    exact Or.inr ⟨⟨code F x,⟨x,hxC⟩,controlled hF _ x hxC hxD⟩,hxC⟩

variable [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α] [LinearOrder β]

theorem monotone_on_cell (F : Finset α) (D : Set α) (f : α → β)
    (hMono : ∀ l u, l < u → (∀ x ∈ Set.Ioo l u, x ∉ F) → Set.Ioo l u ⊆ D →
      StrictMonoOn f (Set.Ioo l u) ∨ StrictAntiOn f (Set.Ioo l u))
    (c : Index F D) : StrictMonoOn f (cell F c.val) ∨ StrictAntiOn f (cell F c.val) := by
  apply OrderedCellMonotonicity.mono_or_anti _ f c.property.1 (connected F c.val)
    (fun x hx => (no_endpoints F c.val x hx).1) (fun x hx => (no_endpoints F c.val x hx).2)
  intro l u hlu hSub
  exact hMono l u hlu (fun x hx => (hSub hx).1) (hSub.trans c.property.2)

end IntegrationInACVF.Section3ACVF.FiniteOrderCellPartition
