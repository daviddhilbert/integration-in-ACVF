module

public import IntegrationSection3.CoarsePartition

@[expose] public section

/-! The canonical support of a set contained in one ball stays inside
that ball. If it contains the parent itself, the set has small complement
there. These are the source-side alternatives needed for 3.11. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport
open IntegrationInACVF.Section3.PuncturedDecomposition

namespace IntegrationInACVF.Section3.SupportInsideBall

variable {X : Type*} {balls : Set (Set X)}

noncomputable def trimmed (F : Finset (Set X)) (P : Set X) : Finset (Set X) := by
  classical
  exact insert P (F.filter fun b => b ⊂ P)

theorem trimmed_support (hl : IsLaminar balls) {P S : Set X} (hP : P ∈ balls)
    (hSP : S ⊆ P) {F : Finset (Set X)} (hF : IsSupport balls F S) :
    IsSupport balls (trimmed F P) S := by
  classical
  change IsSupport balls (insert P (F.filter fun b => b ⊂ P)) S
  constructor
  · intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · exact he.symm ▸ hP
    · exact hF.1 b (Finset.mem_filter.mp hb).1
  · intro x y hxy
    have hp := hxy P (Finset.mem_insert_self _ _)
    by_cases hx : x ∈ P
    · have hy := hp.mp hx
      apply hF.2 x y
      intro b hb
      rcases hl b (hF.1 b hb) P hP with hbP | hPb | hd
      · by_cases he : b = P
        · rw [he]
          exact iff_of_true hx hy
        · exact hxy b (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
            ⟨hb,Set.ssubset_iff_subset_ne.mpr ⟨hbP,he⟩⟩))
      · exact iff_of_true (hPb hx) (hPb hy)
      · exact iff_of_false (fun h => Set.disjoint_left.mp hd h hx)
          (fun h => Set.disjoint_left.mp hd h hy)
    · have hy : y ∉ P := fun h => hx (hp.mpr h)
      exact iff_of_false (fun h => hx (hSP h)) (fun h => hy (hSP h))

theorem support_subset_parent (hl : IsLaminar balls) (htop : (Set.univ : Set X) ∈ balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P S : Set X} (hP : P ∈ balls)
    (hSP : S ⊆ P) {F : Finset (Set X)} (hF : IsMinimalSupport balls F S) :
    ∀ b ∈ F, b ⊆ P := by
  classical
  have hs := minimal_subset_support hl htop hnf hF (trimmed_support hl hP hSP hF.1)
  intro b hb
  have hb' : b ∈ insert P (F.filter fun c => c ⊂ P) := hs hb
  rcases Finset.mem_insert.mp hb' with he | hb
  · exact he ▸ Set.Subset.rfl
  · exact (Finset.mem_filter.mp hb).2.1

theorem parent_region_subset (hl : IsLaminar balls) {P S : Set X} (hSP : S ⊆ P)
    {F : Finset (Set X)} (hF : IsMinimalSupport balls F S) (hPF : P ∈ F) : region F P ⊆ S := by
  classical
  obtain ⟨u,v,huv,hneq⟩ := essential hF hPF
  have hw : ∃ x y : X, x ∈ S ∧ y ∉ S ∧
      ∀ b ∈ F.erase P, x ∈ b ↔ y ∈ b := by
    by_cases hu : u ∈ S
    · exact ⟨u,v,hu,fun hv => hneq (iff_of_true hu hv),huv⟩
    · have hv : v ∈ S := by
        by_contra hv
        exact hneq (iff_of_false hu hv)
      exact ⟨v,u,hv,hu,fun b hb => (huv b hb).symm⟩
  obtain ⟨x,y,hx,hy,hagree⟩ := hw
  have hxP := hSP hx
  have hyP : y ∉ P := by
    intro hyP
    apply hy
    apply (hF.1.2 x y ?_).mp hx
    intro b hb
    by_cases he : b = P
    · rw [he]
      exact iff_of_true hxP hyP
    · exact hagree b (Finset.mem_erase.mpr ⟨he,hb⟩)
  have hxR := region_of_agreement hxP hyP (fun b hb hne =>
    hagree b (Finset.mem_erase.mpr ⟨hne,hb⟩))
  intro z hz
  exact (hF.1.2 z x (region_agreement hl hF.1.1 hPF hz hxR)).mpr hx

theorem parent_mem_small_complement (hl : IsLaminar balls) {P S : Set X}
    (hSP : S ⊆ P) {F : Finset (Set X)} (hF : IsMinimalSupport balls F S) (hPF : P ∈ F) :
    CoarsePartition.SmallIn balls P (P \ S) := by
  classical
  refine ⟨holes F P,fun b hb => ⟨hF.1.1 b (mem_holes.mp hb).1,(mem_holes.mp hb).2.1⟩,?_⟩
  rintro x ⟨hxP,hxS⟩
  by_contra hn
  apply hxS
  apply parent_region_subset hl hSP hF hPF
  rw [region_eq_sdiff_holes]
  exact ⟨hxP,hn⟩

theorem proper_support_of_not_small (hl : IsLaminar balls) (htop : (Set.univ : Set X) ∈ balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P S : Set X} (hP : P ∈ balls)
    (hSP : S ⊆ P) {F : Finset (Set X)} (hF : IsMinimalSupport balls F S)
    (hnot : ¬ CoarsePartition.SmallIn balls P (P \ S)) : ∀ b ∈ F, b ⊂ P := by
  intro b hb
  refine Set.ssubset_iff_subset_ne.mpr ⟨support_subset_parent hl htop hnf hP hSP hF b hb,?_⟩
  intro he
  exact hnot (parent_mem_small_complement hl hSP hF (he ▸ hb))

end IntegrationInACVF.Section3.SupportInsideBall
