import IntegrationSection3ACVF.OrderedFiniteCellCount
import Mathlib.Tactic

/-! The elementary one-dimensional cell count: a closed interval has
one more point cell than open cell, whereas an interval with no least
point has equally many. Decomposition premises remain explicit here. -/

open Set Classical

namespace IntegrationInACVF.Section3ACVF.OrderedCellDecomposition

variable {α ι : Type*} [LinearOrder α]

structure Data (D : Set α) (ι : Type*) where
  points : Finset α
  cells : ι → Set α
  cover : ∀ x, x ∈ D ↔ x ∈ points ∨ ∃ i, x ∈ cells i
  points_disjoint : ∀ i, Disjoint (points : Set α) (cells i)
  cells_disjoint : ∀ i j, i ≠ j → Disjoint (cells i) (cells j)
  nonempty : ∀ i, (cells i).Nonempty
  connected : ∀ i, OrdConnected (cells i)
  no_min : ∀ i, ∀ x ∈ cells i, ∃ y ∈ cells i, y < x
  no_max : ∀ i, ∀ x ∈ cells i, ∃ y ∈ cells i, x < y
  right : ι → α
  isLUB : ∀ i, IsLUB (cells i) (right i)
  endpoint_mem : ∀ i, right i ∈ D

variable [DenselyOrdered α]

theorem cardinal {D : Set α} (K : Data D ι) (hD : OrdConnected D) :
    Nat.card ι = {p | p ∈ K.points ∧ ∃ x ∈ D, x < p}.ncard :=
  OrderedFiniteCellCount.cardinal D K.points hD K.points.finite_toSet K.cells K.right
    K.cover K.points_disjoint K.cells_disjoint K.nonempty K.connected K.no_min K.no_max K.isLUB K.endpoint_mem

theorem closed_count (a b : α) (hab : a ≤ b) (K : Data (Set.Icc a b) ι) :
    K.points.card = Nat.card ι + 1 := by
  have hSub : (K.points : Set α) ⊆ Set.Icc a b := fun x hx => (K.cover x).mpr (Or.inl hx)
  have ha : a ∈ K.points := by
    have haD : a ∈ Set.Icc a b := ⟨le_rfl,hab⟩
    rcases (K.cover a).mp haD with h | ⟨i,hai⟩
    · exact h
    · obtain ⟨y,hy,hya⟩ := K.no_min i a hai
      have hyD : y ∈ Set.Icc a b := (K.cover y).mpr (Or.inr ⟨i,hy⟩)
      exact ((not_lt_of_ge hyD.1) hya).elim
  have hQ : {p | p ∈ K.points ∧ ∃ x ∈ Set.Icc a b, x < p} =
      (K.points : Set α) \ {a} := by
    ext p
    constructor
    · rintro ⟨hp,x,hx,hxp⟩
      exact ⟨hp,fun he => (not_lt_of_ge hx.1) (he ▸ hxp)⟩
    · rintro ⟨hp,hpa⟩
      have hap : a < p := lt_of_le_of_ne (hSub hp).1 (Ne.symm hpa)
      exact ⟨hp,a,⟨le_rfl,hab⟩,hap⟩
  have hCount := cardinal K Set.ordConnected_Icc
  rw [hQ] at hCount
  have hRemove := Set.ncard_sdiff_singleton_add_one (s := (K.points : Set α)) ha K.points.finite_toSet
  rw [← hCount] at hRemove
  simpa only [Set.ncard_coe_finset] using hRemove.symm

theorem noMin_count {D : Set α} (K : Data D ι) (hD : OrdConnected D)
    (hNoMin : ∀ p ∈ D, ∃ x ∈ D, x < p) : K.points.card = Nat.card ι := by
  have hQ : {p | p ∈ K.points ∧ ∃ x ∈ D, x < p} = (K.points : Set α) := by
    ext p
    exact ⟨fun h => h.1,fun hp => ⟨hp,hNoMin p ((K.cover p).mpr (Or.inl hp))⟩⟩
  have hCount := cardinal K hD
  rw [hQ,Set.ncard_coe_finset] at hCount
  exact hCount.symm

theorem closed_noMin_obstruction (a b : α) (hab : a ≤ b) (K : Data (Set.Icc a b) ι)
    {D : Set α} (L : Data D ι) (hD : OrdConnected D) (hNoMin : ∀ p ∈ D, ∃ x ∈ D, x < p)
    (hPoints : K.points.card = L.points.card) : False := by
  have hK := closed_count a b hab K
  have hL := noMin_count L hD hNoMin
  omega

end IntegrationInACVF.Section3ACVF.OrderedCellDecomposition
