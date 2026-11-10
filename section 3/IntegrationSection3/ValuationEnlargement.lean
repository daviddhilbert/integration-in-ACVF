module

public import IntegrationSection3.ValuationRadius

@[expose] public section

/-! Strict closed-ball enlargements at an intermediate valuation radius.
The eventual ACVF bridge must choose the radii intrinsically over its
original base. These lemmas concern only the valuation geometry. -/

namespace IntegrationInACVF.Section3.ValuationEnlargement

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem strict_enlargement (v : Valuation K Γ) (a r t : K) {H : Set K}
    (hbound : H ⊆ {x | v (x-a) ≤ v r}) (hrt : v r < v t) :
    H ⊂ {x | v (x-a) ≤ v t} := by
  refine ⟨fun x hx => (hbound hx).trans hrt.le,?_⟩
  intro hrev
  have hx : a+t ∈ H := hrev (by simp only [Set.mem_ofPred_eq,add_sub_cancel_left,le_refl])
  have hn := hbound hx
  exact not_le_of_gt hrt (by simpa only [Set.mem_ofPred_eq,add_sub_cancel_left] using hn)

theorem closed_ssubset_closed (v : Valuation K Γ) (a b t s : K)
    (ha : v (a-b) ≤ v s) (hts : v t < v s) :
    {x | v (x-a) ≤ v t} ⊂ {x | v (x-b) ≤ v s} := by
  refine ⟨?_,?_⟩
  · intro x hx
    change v (x-b) ≤ v s
    have he : x-b = (x-a)+(a-b) := by ring
    rw [he]
    exact (v.map_add _ _).trans (max_le (hx.trans hts.le) ha)
  · intro hrev
    exact not_le_of_gt hts
      (ValuationRadius.closed_radius_le_of_subset v b a s t hrev)

theorem closed_ssubset_open (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (a b t s : K) (ha : v (a-b) < v s) (hts : v t < v s) :
    {x | v (x-a) ≤ v t} ⊂ {x | v (x-b) < v s} := by
  refine ⟨?_,?_⟩
  · intro x hx
    change v (x-b) < v s
    have he : x-b = (x-a)+(a-b) := by ring
    rw [he]
    exact (v.map_add _ _).trans_lt (max_lt (hx.trans_lt hts) ha)
  · intro hrev
    have hs : s ≠ 0 := by
      intro hz
      rw [hz,map_zero] at ha
      exact not_lt_of_ge (zero_le : (0 : Γ) ≤ v (a-b)) ha
    exact not_le_of_gt hts
      (ValuationRadius.open_radius_le_of_subset_closed v hdense b a s t hs hrev)

end IntegrationInACVF.Section3.ValuationEnlargement
