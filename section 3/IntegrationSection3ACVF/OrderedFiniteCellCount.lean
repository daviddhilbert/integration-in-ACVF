import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max

/-! Count a finite disjoint decomposition into points and open order
cells by sending each cell to its right endpoint. Actual least upper
bounds are explicit, so nonprincipal cuts cannot enter the argument. -/

open Set Classical

namespace IntegrationInACVF.Section3ACVF.OrderedFiniteCellCount

variable {α ι : Type*} [LinearOrder α] [DenselyOrdered α]

theorem cardinal (D P : Set α) (hDConnected : OrdConnected D) (hP : P.Finite) (C : ι → Set α) (r : ι → α)
    (hPartition : ∀ x, x ∈ D ↔ x ∈ P ∨ ∃ i, x ∈ C i)
    (hPoints : ∀ i, Disjoint P (C i))
    (hDisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hNonempty : ∀ i, (C i).Nonempty) (hConnected : ∀ i, OrdConnected (C i))
    (hNoMin : ∀ i, ∀ x ∈ C i, ∃ y ∈ C i, y < x)
    (hNoMax : ∀ i, ∀ x ∈ C i, ∃ y ∈ C i, x < y)
    (hLUB : ∀ i, IsLUB (C i) (r i)) (hEndpoint : ∀ i, r i ∈ D) :
    Nat.card ι = {p | p ∈ P ∧ ∃ x ∈ D, x < p}.ncard := by
  classical
  have hBelow (i : ι) (t : α) (ht : t < r i) : ∃ z ∈ C i, t < z := by
    by_contra hn
    have htUpper : t ∈ upperBounds (C i) := by
      intro z hz
      by_contra hzt
      exact hn ⟨z,hz,lt_of_not_ge hzt⟩
    exact (not_lt_of_ge ((hLUB i).2 htUpper)) ht
  have hStrict (i : ι) (x : α) (hx : x ∈ C i) : x < r i := by
    obtain ⟨y,hy,hxy⟩ := hNoMax i x hx
    exact hxy.trans_le ((hLUB i).1 hy)
  have hRP (i : ι) : r i ∈ P := by
    by_contra hn
    obtain ⟨j,hj⟩ := ((hPartition (r i)).mp (hEndpoint i)).resolve_left hn
    obtain ⟨y,hy,hyr⟩ := hNoMin j (r i) hj
    obtain ⟨z,hz,hyz⟩ := hBelow i y hyr
    have hzJ : z ∈ C j := (hConnected j).out hy hj ⟨hyz.le,(hLUB i).1 hz⟩
    have hij : i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (hDisjoint i j hij) hz hzJ
    subst j
    exact (lt_irrefl (r i)) (hStrict i (r i) hj)
  have hInj : Function.Injective r := by
    intro i j he
    by_contra hij
    obtain ⟨x,hx⟩ := hNonempty i
    obtain ⟨y,hy,hxy⟩ := hBelow j x (he ▸ hStrict i x hx)
    obtain ⟨z,hz,hyz⟩ := hBelow i y (he.symm ▸ hStrict j y hy)
    have hyI : y ∈ C i := (hConnected i).out hx hz ⟨hxy.le,hyz.le⟩
    exact Set.disjoint_left.mp (hDisjoint i j hij) hyI hy
  let Q : Set α := {p | p ∈ P ∧ ∃ x ∈ D, x < p}
  have hMap (i : ι) : r i ∈ Q := by
    obtain ⟨x,hx⟩ := hNonempty i
    exact ⟨hRP i,x,(hPartition x).mpr (Or.inr ⟨i,hx⟩),hStrict i x hx⟩
  have hSurj : ∀ p ∈ Q, ∃ i, r i = p := by
    rintro p ⟨hp,x,hxD,hxp⟩
    let L := hP.toFinset.filter (· < p)
    have hNear : ∃ z, x < z ∧ z < p ∧ ∀ q ∈ P, q < p → q < z := by
      by_cases hL : L.Nonempty
      · have hLp : L.max' hL < p := (Finset.mem_filter.mp (L.max'_mem hL)).2
        obtain ⟨z,hz,hzp⟩ := exists_between (max_lt hxp hLp)
        refine ⟨z,(le_max_left _ _).trans_lt hz,hzp,?_⟩
        intro q hq hqp
        have hqL : q ∈ L := Finset.mem_filter.mpr ⟨hP.mem_toFinset.mpr hq,hqp⟩
        exact (L.le_max' q hqL).trans_lt ((le_max_right _ _).trans_lt hz)
      · obtain ⟨z,hxz,hzp⟩ := exists_between hxp
        refine ⟨z,hxz,hzp,?_⟩
        intro q hq hqp
        exact (hL ⟨q,Finset.mem_filter.mpr ⟨hP.mem_toFinset.mpr hq,hqp⟩⟩).elim
    obtain ⟨z,hxz,hzp,hGap⟩ := hNear
    have hpD : p ∈ D := (hPartition p).mpr (Or.inl hp)
    have hzD : z ∈ D := hDConnected.out hxD hpD ⟨hxz.le,hzp.le⟩
    have hzP : z ∉ P := fun hzP => (lt_irrefl z) (hGap z hzP hzp)
    obtain ⟨i,hzi⟩ := ((hPartition z).mp hzD).resolve_left hzP
    have hrLe : r i ≤ p := by
      apply (hLUB i).2
      intro y hy
      by_contra hpy
      have hpC : p ∈ C i := (hConnected i).out hzi hy ⟨hzp.le,(lt_of_not_ge hpy).le⟩
      exact Set.disjoint_left.mp (hPoints i) hp hpC
    refine ⟨i,le_antisymm hrLe ?_⟩
    by_contra hn
    have hrp : r i < p := lt_of_not_ge hn
    exact (not_lt_of_gt (hStrict i z hzi)) (hGap (r i) (hRP i) hrp)
  have hBij : Set.BijOn r Set.univ Q :=
    ⟨fun i _ => hMap i,fun i _ j _ he => hInj he,fun p hp => by
      obtain ⟨i,hi⟩ := hSurj p hp
      exact ⟨i,Set.mem_univ _,hi⟩⟩
  simpa only [Set.ncard_univ] using hBij.ncard_eq

end IntegrationInACVF.Section3ACVF.OrderedFiniteCellCount
