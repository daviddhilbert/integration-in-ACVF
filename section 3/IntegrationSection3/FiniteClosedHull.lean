module

public import IntegrationSection3.FiniteBallHulls

@[expose] public section

/-! Intrinsic radius of the smallest closed ball containing a finite
nonempty family of balls. This is valuation geometry, not a new ball sort. -/

open Set

namespace IntegrationInACVF.Section3.FiniteClosedHull

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def IsHull (v : Valuation K Γ) (S : Set K) (a r : K) : Prop :=
  S ⊆ {x | v (x-a) ≤ v r} ∧
    ∀ b s : K, S ⊆ {x | v (x-b) ≤ v s} → v r ≤ v s

theorem radius_unique (v : Valuation K Γ) {S : Set K} {a r b s : K}
    (h : IsHull v S a r) (h' : IsHull v S b s) : v r = v s :=
  le_antisymm (h.2 b s h'.1) (h'.2 a r h.1)

theorem open_hull_subset (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (a r b s : K) (hr : r ≠ 0)
    (hsub : {x | v (x-a) < v r} ⊆ {x | v (x-b) ≤ v s}) :
    {x | v (x-a) ≤ v r} ⊆ {x | v (x-b) ≤ v s} := by
  have hrad := ValuationRadius.open_radius_le_of_subset_closed v hdense a b r s hr hsub
  have ha : v (a-b) ≤ v s := hsub (by
    simpa only [Set.mem_ofPred_eq,sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr)))
  intro x hx
  change v (x-b) ≤ v s
  have he : x-b = (x-a)+(a-b) := by ring
  rw [he]
  exact (v.map_add _ _).trans (max_le (hx.trans hrad) ha)

theorem exists_hull (v : Valuation K Γ) (F : Finset (K × K)) (hne : F.Nonempty) :
    ∃ a r : K, IsHull v {x | ∃ p ∈ F, v (x-p.1) ≤ v p.2} a r := by
  classical
  obtain ⟨p0,hp0⟩ := hne
  let a := p0.1
  let G := F.image Prod.snd ∪ F.image (fun p => p.1-a)
  have hGne : G.Nonempty := ⟨p0.2,Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨p0,hp0,rfl⟩)⟩
  obtain ⟨r,hr,hmax⟩ := G.exists_max_image v hGne
  have hrad (p : K × K) (hp : p ∈ F) : v p.2 ≤ v r :=
    hmax _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  have hcentre (p : K × K) (hp : p ∈ F) : v (p.1-a) ≤ v r :=
    hmax _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  refine ⟨a,r,?_,?_⟩
  · rintro x ⟨p,hp,hx⟩
    change v (x-a) ≤ v r
    have he : x-a = (x-p.1)+(p.1-a) := by ring
    rw [he]
    exact (v.map_add _ _).trans (max_le (hx.trans (hrad p hp)) (hcentre p hp))
  · intro b s hs
    have hpoint (p : K × K) (hp : p ∈ F) : v (p.1-b) ≤ v s := hs
      ⟨p,hp,by simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v p.2)⟩
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      exact ValuationRadius.closed_radius_le_of_subset v p.1 b p.2 s
        (fun x hx => hs ⟨p,hp,hx⟩)
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      have he : p.1-a = (p.1-b)-(a-b) := by ring
      rw [he]
      exact (v.map_sub _ _).trans (max_le (hpoint p hp) (hpoint p0 hp0))

theorem radius_lt_of_open_cover (v : Valuation K Γ)
    (hdense : ∀ r s : K, v r < v s → ∃ t : K, v r < v t ∧ v t < v s)
    (F : Finset (K × K)) (a r c s : K) (hs : s ≠ 0)
    (hF : ∀ p ∈ F, {x | v (x-p.1) ≤ v p.2} ⊆ {x | v (x-c) < v s})
    (hHull : IsHull v {x | ∃ p ∈ F, v (x-p.1) ≤ v p.2} a r) : v r < v s := by
  classical
  let G := F.image Prod.snd ∪ F.image (fun p => p.1-c)
  have hG : ∀ x ∈ G, v x < v s := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact ValuationRadius.closed_radius_lt_of_subset_open v p.1 c p.2 s (hF p hp)
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      apply hF p hp
      change v (p.1-p.1) ≤ v p.2
      simpa only [sub_self,map_zero] using (zero_le : (0 : Γ) ≤ v p.2)
  obtain ⟨t,hts,ht⟩ := FiniteBallHulls.finite_strict_bound v hdense G s hs hG
  apply lt_of_le_of_lt (hHull.2 c t ?_) hts
  rintro x ⟨p,hp,hx⟩
  have hrad := ht p.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  have hcentre := ht (p.1-c) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  change v (x-c) ≤ v t
  have he : x-c = (x-p.1)+(p.1-c) := by ring
  rw [he]
  exact ((v.map_add _ _).trans_lt (max_lt (hx.trans_lt hrad) hcentre)).le

/-- Replacing finitely many sets by their individual closed hulls preserves
all closed covering balls. Centres used in this existence proof need not be
definable; the resulting radius is characterized intrinsically by IsHull. -/
theorem exists_of_finite_hulls {ι : Type*} (v : Valuation K Γ)
    (F : Finset ι) (hne : F.Nonempty) (C : ι → Set K) (a r : ι → K)
    (hsub : ∀ i ∈ F, C i ⊆ {x | v (x-a i) ≤ v (r i)})
    (hminimal : ∀ i ∈ F, ∀ b s : K, C i ⊆ {x | v (x-b) ≤ v s} →
      {x | v (x-a i) ≤ v (r i)} ⊆ {x | v (x-b) ≤ v s}) :
    ∃ b s : K, IsHull v {x | ∃ i ∈ F, x ∈ C i} b s := by
  classical
  let G := F.image (fun i => (a i,r i))
  have hG : G.Nonempty := hne.image _
  obtain ⟨b,s,hs⟩ := exists_hull v G hG
  have he (c t : K) :
      ({x | ∃ i ∈ F, x ∈ C i} : Set K) ⊆ {x | v (x-c) ≤ v t} ↔
      ({x | ∃ p ∈ G, v (x-p.1) ≤ v p.2} : Set K) ⊆ {x | v (x-c) ≤ v t} := by
    constructor
    · intro hc x hx
      obtain ⟨p,hp,hxp⟩ := hx
      obtain ⟨i,hi,hpi⟩ := Finset.mem_image.mp hp
      rw [← hpi] at hxp
      exact hminimal i hi c t (fun y hy => hc ⟨i,hi,hy⟩) hxp
    · intro hc x hx
      obtain ⟨i,hi,hxi⟩ := hx
      exact hc ⟨(a i,r i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,hsub i hi hxi⟩
  exact ⟨b,s,(he b s).mpr hs.1,fun c t hc => hs.2 c t ((he c t).mp hc)⟩

theorem radius_ne_zero_of_infinite (v : Valuation K Γ) {S : Set K} (hS : S.Infinite)
    {a r : K} (hHull : IsHull v S a r) : r ≠ 0 := by
  intro hr
  apply hS
  apply (Set.finite_singleton a).subset
  intro x hx
  have hle := hHull.1 hx
  rw [hr,map_zero] at hle
  have hz : v (x-a) = 0 := le_antisymm hle zero_le
  exact sub_eq_zero.mp (v.zero_iff.mp hz)

end IntegrationInACVF.Section3.FiniteClosedHull
