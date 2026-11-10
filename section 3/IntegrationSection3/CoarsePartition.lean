module

public import IntegrationSection3.MinimalBallSupport

@[expose] public section

/-! The finite ball-support geometry behind the unique outer preimage
piece in Lemma 3.8. Definability of the distinguished index is separate;
this module proves the semantic uniqueness without naming any support. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport
open IntegrationInACVF.Section3.PuncturedDecomposition

namespace IntegrationInACVF.Section3.CoarsePartition

variable {X J : Type*} {balls : Set (Set X)}

/-- Coverable by finitely many proper balls in the given parent. -/
def SmallIn (balls : Set (Set X)) (P S : Set X) : Prop :=
  ∃ H : Finset (Set X), (∀ h ∈ H, h ∈ balls ∧ h ⊂ P) ∧
    S ⊆ {x | ∃ h ∈ H, x ∈ h}

def CoveredBy (balls : Set (Set X)) (P S : Set X) (N : ℕ) : Prop :=
  ∃ H : Finset (Set X), H.card ≤ N ∧ (∀ h ∈ H, h ∈ balls ∧ h ⊂ P) ∧
    S ⊆ {x | ∃ h ∈ H, x ∈ h}

theorem region_not_small (hnf : AvoidsFiniteProperSubballs balls)
    {P : Set X} (hP : P ∈ balls) {F : Finset (Set X)}
    (hF : ∀ b ∈ F, b ∈ balls) : ¬ SmallIn balls P (region F P) := by
  classical
  rintro ⟨H,hH,hcov⟩
  let G := (F.filter fun b => b ⊂ P) ∪ H
  obtain ⟨x,hx,havoid⟩ := hnf P hP G (by
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨hb,hbp⟩ := Finset.mem_filter.mp hb
      exact ⟨hF b hb,hbp⟩
    · exact hH b hb)
  have hxreg : x ∈ region F P :=
    ⟨hx,fun b hb hbp => havoid b
      (Finset.mem_union_left H (Finset.mem_filter.mpr ⟨hb,hbp⟩))⟩
  obtain ⟨h,hh,hxh⟩ := hcov hxreg
  exact havoid h (Finset.mem_union_right _ hh) hxh

theorem common_support {T : Set J} (hT : T.Finite) {C : J → Set X}
    (hC : ∀ j ∈ T, HasFiniteBallSupport balls (C j)) :
    ∃ F : Finset (Set X), (∀ b ∈ F, b ∈ balls) ∧ ∀ j ∈ T, Supports F (C j) := by
  classical
  let := hT.fintype
  let G : T → Finset (Set X) := fun j => Classical.choose (hC j.val j.property)
  have hG (j : T) := Classical.choose_spec (hC j.val j.property)
  let F := Finset.univ.biUnion G
  refine ⟨F,?_,?_⟩
  · intro b hb
    obtain ⟨j,_,hbj⟩ := Finset.mem_biUnion.mp hb
    exact (hG j).1 b hbj
  · intro j hj x y hxy
    apply (hG ⟨j,hj⟩).2 x y
    intro b hb
    exact hxy b (Finset.mem_biUnion.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,hb⟩)

/-- In a disjoint partition of a punctured ball by finitely supported
sets, exactly one part cannot be covered by finitely many proper subballs.
The same finite support works for all parts; a finite family supplies it
by common_support. -/
theorem outer_piece_cover (hl : IsLaminar balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P : Set X} (hP : P ∈ balls)
    {H F : Finset (Set X)} (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ P)
    (hF : ∀ b ∈ F, b ∈ balls) {T : Set J} {C : J → Set X}
    (hsupport : ∀ j ∈ T, Supports F (C j))
    (hsub : ∀ j ∈ T, C j ⊆ P)
    (hcover : P \ {x | ∃ h ∈ H, x ∈ h} ⊆ {x | ∃ j ∈ T, x ∈ C j})
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k)) :
    ∃ G : Finset (Set X), (∀ b ∈ G, b ∈ balls ∧ b ⊂ P) ∧
      ∃ j ∈ T, ¬ SmallIn balls P (C j) ∧
        ∀ k ∈ T, k ≠ j → C k ⊆ {x | ∃ b ∈ G, x ∈ b} := by
  classical
  let E := F ∪ H
  have hE : ∀ b ∈ E, b ∈ balls := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hF b) (fun hb => (hH b hb).1)
  let G := E.filter fun b => b ⊂ P
  obtain ⟨x,hx,havoid⟩ := hnf P hP G (by
    intro b hb
    obtain ⟨hb,hbp⟩ := Finset.mem_filter.mp hb
    exact ⟨hE b hb,hbp⟩)
  have hxreg : x ∈ region E P :=
    ⟨hx,fun b hb hbp => havoid b (Finset.mem_filter.mpr ⟨hb,hbp⟩)⟩
  have hxA : x ∈ P \ {x | ∃ h ∈ H, x ∈ h} := by
    refine ⟨hx,?_⟩
    rintro ⟨h,hh,hxh⟩
    exact hxreg.2 h (Finset.mem_union_right F hh) (hH h hh).2 hxh
  obtain ⟨j,hj,hxj⟩ := hcover hxA
  have hregsub : region E P ⊆ C j := by
    intro y hy
    apply (hsupport j hj x y ?_).mp hxj
    intro b hb
    have hbE : b ∈ E := Finset.mem_union_left H hb
    exact (region_mem_iff_subset hl hE hP hxreg hbE).trans
      (region_mem_iff_subset hl hE hP hy hbE).symm
  have hjbig : ¬ SmallIn balls P (C j) := by
    rintro ⟨K,hK,hcov⟩
    exact region_not_small hnf hP hE ⟨K,hK,hregsub.trans hcov⟩
  refine ⟨G,fun b hb => ⟨hE b (Finset.mem_filter.mp hb).1,
    (Finset.mem_filter.mp hb).2⟩,j,hj,hjbig,?_⟩
  intro k hk hkj y hy
  have hyP := hsub k hk hy
  have hyn : y ∉ region E P := by
    intro hyr
    exact Set.disjoint_left.mp (hdis hk hj hkj) hy (hregsub hyr)
  have hex : ∃ b ∈ E, b ⊂ P ∧ y ∈ b := by
    by_contra hn
    apply hyn
    exact ⟨hyP,fun b hb hbp hyb => hn ⟨b,hb,hbp,hyb⟩⟩
  obtain ⟨b,hb,hbp,hyb⟩ := hex
  exact ⟨b,Finset.mem_filter.mpr ⟨hb,hbp⟩,hyb⟩

/-- A single finite bound detects the unique outer part. The bound is a
natural number, not a new model parameter. Its first-order definability is
proved separately using a fixed finite tuple of ball codes. -/
theorem unique_outer_piece_at_bound (hl : IsLaminar balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P : Set X} (hP : P ∈ balls)
    {H F : Finset (Set X)} (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ P)
    (hF : ∀ b ∈ F, b ∈ balls) {T : Set J} {C : J → Set X}
    (hsupport : ∀ j ∈ T, Supports F (C j))
    (hsub : ∀ j ∈ T, C j ⊆ P)
    (hcover : P \ {x | ∃ h ∈ H, x ∈ h} ⊆ {x | ∃ j ∈ T, x ∈ C j})
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k)) :
    ∃ N : ℕ, ∃! j, j ∈ T ∧ ¬ CoveredBy balls P (C j) N := by
  obtain ⟨G,hG,j,hj,hjbig,hother⟩ := outer_piece_cover hl hnf hP hH hF
    hsupport hsub hcover hdis
  refine ⟨G.card,j,⟨hj,?_⟩,?_⟩
  · rintro ⟨K,_,hK,hcov⟩
    exact hjbig ⟨K,hK,hcov⟩
  · rintro k ⟨hk,hkn⟩
    by_contra hkj
    exact hkn ⟨G,le_rfl,hG,hother k hk hkj⟩

end IntegrationInACVF.Section3.CoarsePartition
