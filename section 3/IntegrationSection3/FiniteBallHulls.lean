module

public import IntegrationSection3.ValuationEnlargement
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Finite valuative hulls inside an open ball. The density input concerns
actual values and is supplied by the checked ACVF bridge. -/

open Set

namespace IntegrationInACVF.Section3.FiniteBallHulls

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem finite_strict_bound (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (F : Finset K) (r : K) (hr : r ≠ 0) (hF : ∀ x ∈ F, v x < v r) :
    ∃ t : K, v t < v r ∧ ∀ x ∈ F, v x < v t := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨x,hx,hmax⟩ := F.exists_max_image v hne
    obtain ⟨t,hxt,htr⟩ := hdense x r (hF x hx)
    exact ⟨t,htr,fun y hy => (hmax y hy).trans_lt hxt⟩
  · obtain ⟨t,_,htr⟩ := hdense 0 r (by
      simpa only [map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr)))
    exact ⟨t,htr,fun x hx => (hne ⟨x,hx⟩).elim⟩

theorem open_ssubset_open (v : Valuation K Γ) (c t r : K) (htr : v t < v r) :
    {x | v (x-c) < v t} ⊂ {x | v (x-c) < v r} := by
  refine ⟨fun _ hx => hx.trans htr,?_⟩
  intro hrev
  have hx : c+t ∈ {x | v (x-c) < v r} := by
    simpa only [Set.mem_ofPred_eq,add_sub_cancel_left] using htr
  have hbad := hrev hx
  exact lt_irrefl (v t) (by simpa only [Set.mem_ofPred_eq,add_sub_cancel_left] using hbad)

theorem finite_points_in_proper_open (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (F : Finset K) (c r : K) (hr : r ≠ 0) (hF : ∀ x ∈ F, v (x-c) < v r) :
    ∃ t : K, ({x | v (x-c) < v t} ⊂ {x | v (x-c) < v r}) ∧
      ∀ x ∈ F, v (x-c) < v t := by
  classical
  have hf : ∀ x ∈ F.image (fun x => x-c), v x < v r := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hF y hy
  obtain ⟨t,htr,ht⟩ := finite_strict_bound v hdense _ r hr hf
  exact ⟨t,open_ssubset_open v c t r htr,
    fun x hx => ht (x-c) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩

/-- Finitely many closed balls lying in one open ball are all contained
in a strictly smaller open ball. Both centre distances and radii enter the
finite bound; bounding the radii alone would be insufficient. -/
theorem finite_closed_balls_in_proper_open (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (F : Finset (K × K)) (c r : K) (hr : r ≠ 0)
    (hF : ∀ p ∈ F, {x | v (x-p.1) ≤ v p.2} ⊆ {x | v (x-c) < v r}) :
    ∃ t : K, ({x | v (x-c) < v t} ⊂ {x | v (x-c) < v r}) ∧
      ∀ p ∈ F, {x | v (x-p.1) ≤ v p.2} ⊆ {x | v (x-c) < v t} := by
  classical
  let G := F.image Prod.snd ∪ F.image (fun p => p.1-c)
  have hG : ∀ x ∈ G, v x < v r := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact ValuationRadius.closed_radius_lt_of_subset_open v p.1 c p.2 r (hF p hp)
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      apply hF p hp
      change v (p.1-p.1) ≤ v p.2
      simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v p.2)
  obtain ⟨t,htr,ht⟩ := finite_strict_bound v hdense G r hr hG
  refine ⟨t,open_ssubset_open v c t r htr,?_⟩
  intro p hp x hx
  have hrad : v p.2 < v t := ht p.2
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  have hcentre : v (p.1-c) < v t := ht (p.1-c)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  have he : x-c = (x-p.1)+(p.1-c) := by ring
  change v (x-c) < v t
  rw [he]
  exact (v.map_add _ _).trans_lt (max_lt (hx.trans_lt hrad) hcentre)

end IntegrationInACVF.Section3.FiniteBallHulls
