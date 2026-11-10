module

public import IntegrationSection3.BallSupport
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-! The finite laminar geometry underlying the first step of Lemma 3.6.
This establishes disjoint punctured pieces, without claiming the later
original-base definability or equality of their primitive invariants. -/

open Set

namespace IntegrationInACVF.Section3.PuncturedDecomposition

variable {X : Type*}

/-- The part of a support ball outside all strictly smaller support balls. -/
def region (F : Finset (Set X)) (b : Set X) : Set X :=
  {x | x ∈ b ∧ ∀ c ∈ F, c ⊂ b → x ∉ c}

/-- Only maximal proper support balls are needed as holes. -/
noncomputable def holes (F : Finset (Set X)) (b : Set X) : Finset (Set X) := by
  classical
  exact F.filter fun c => c ⊂ b ∧ ∀ d ∈ F, d ⊂ b → c ⊆ d → d ⊆ c

theorem mem_holes {F : Finset (Set X)} {b c : Set X} :
    c ∈ holes F b ↔ c ∈ F ∧ c ⊂ b ∧ ∀ d ∈ F, d ⊂ b → c ⊆ d → d ⊆ c := by
  classical
  exact Finset.mem_filter

theorem proper_subset_in_hole {F : Finset (Set X)} {b c : Set X}
    (hc : c ∈ F) (hcb : c ⊂ b) : ∃ d ∈ holes F b, c ⊆ d := by
  classical
  let H := F.filter fun d => d ⊂ b
  obtain ⟨d,hcd,hd,hmax⟩ := H.exists_le_maximal (Finset.mem_filter.mpr ⟨hc,hcb⟩)
  obtain ⟨hdF,hdb⟩ := Finset.mem_filter.mp hd
  exact ⟨d,mem_holes.mpr ⟨hdF,hdb,fun e he heb hde =>
    hmax (Finset.mem_filter.mpr ⟨he,heb⟩) hde⟩,hcd⟩

theorem region_eq_sdiff_holes (F : Finset (Set X)) (b : Set X) :
    region F b = b \ {x | ∃ c ∈ holes F b, x ∈ c} := by
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨hx,?_⟩
    rintro ⟨c,hc,hxc⟩
    exact hn c (mem_holes.mp hc).1 (mem_holes.mp hc).2.1 hxc
  · rintro ⟨hx,hn⟩
    refine ⟨hx,fun c hc hcb hxc => ?_⟩
    obtain ⟨d,hd,hcd⟩ := proper_subset_in_hole hc hcb
    exact hn ⟨d,hd,hcd hxc⟩

theorem holes_disjoint {balls : Set (Set X)} (hl : IsLaminar balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls) (b : Set X) :
    (holes F b : Set (Set X)).Pairwise Disjoint := by
  intro c hc d hd hne
  obtain ⟨hcF,hcb,hcm⟩ := mem_holes.mp hc
  obtain ⟨hdF,hdb,hdm⟩ := mem_holes.mp hd
  rcases hl c (hF c hcF) d (hF d hdF) with hcd | hdc | hdis
  · exact (hne (Set.Subset.antisymm hcd (hcm d hdF hdb hcd))).elim
  · exact (hne (Set.Subset.antisymm (hdm c hcF hcb hdc) hdc)).elim
  · exact hdis

theorem regions_disjoint {balls : Set (Set X)} (hl : IsLaminar balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls) :
    (F : Set (Set X)).Pairwise fun b c => Disjoint (region F b) (region F c) := by
  intro b hb c hc hne
  apply Set.disjoint_left.mpr
  rintro x ⟨hxb,hbn⟩ ⟨hxc,hcn⟩
  rcases hl b (hF b hb) c (hF c hc) with hbc | hcb | hd
  · exact hcn b hb (Set.ssubset_iff_subset_ne.mpr ⟨hbc,hne⟩) hxb
  · exact hbn c hc (Set.ssubset_iff_subset_ne.mpr ⟨hcb,hne.symm⟩) hxc
  · exact Set.disjoint_left.mp hd hxb hxc

theorem region_agreement {balls : Set (Set X)} (hl : IsLaminar balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls) {b : Set X} (hb : b ∈ F)
    {x y : X} (hx : x ∈ region F b) (hy : y ∈ region F b) :
    ∀ c ∈ F, x ∈ c ↔ y ∈ c := by
  intro c hc
  rcases hl b (hF b hb) c (hF c hc) with hbc | hcb | hd
  · exact iff_of_true (hbc hx.1) (hbc hy.1)
  · by_cases he : c = b
    · exact iff_of_true (he.symm ▸ hx.1) (he.symm ▸ hy.1)
    · have hs := Set.ssubset_iff_subset_ne.mpr ⟨hcb,he⟩
      exact iff_of_false (hx.2 c hc hs) (hy.2 c hc hs)
  · exact iff_of_false (fun h => Set.disjoint_left.mp hd hx.1 h)
      (fun h => Set.disjoint_left.mp hd hy.1 h)

theorem exists_region {F : Finset (Set X)} {D : Set X} (hD : D ∈ F)
    {x : X} (hx : x ∈ D) : ∃ b ∈ F, x ∈ region F b := by
  classical
  let H := F.filter fun b => x ∈ b
  obtain ⟨b,hb,hmin⟩ := H.exists_minimal ⟨D,Finset.mem_filter.mpr ⟨hD,hx⟩⟩
  obtain ⟨hbF,hxb⟩ := Finset.mem_filter.mp hb
  refine ⟨b,hbF,hxb,?_⟩
  intro c hc hcb hxc
  exact hcb.2 (hmin (Finset.mem_filter.mpr ⟨hc,hxc⟩) hcb.1)

/-- A finite-support set is a finite disjoint union of regions, each a
support ball minus pairwise disjoint proper support balls. No definability
of the chosen finite support over the parameter base is asserted here. -/
theorem finite_punctured_decomposition {balls : Set (Set X)} (hl : IsLaminar balls)
    {D S : Set X} (hD : D ∈ balls) (hSD : S ⊆ D) (hS : HasFiniteBallSupport balls S) :
    ∃ F G : Finset (Set X), (∀ b ∈ F, b ∈ balls) ∧ G ⊆ F ∧
      (∀ b ∈ G, (region F b).Nonempty) ∧
      (G : Set (Set X)).Pairwise (fun b c => Disjoint (region F b) (region F c)) ∧
      S = {x | ∃ b ∈ G, x ∈ region F b} ∧
      ∀ b ∈ G, (holes F b : Set (Set X)).Pairwise Disjoint := by
  classical
  obtain ⟨E,hE,hES⟩ := hS
  let F := insert D E
  have hF : ∀ b ∈ F, b ∈ balls := by
    intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · exact he.symm ▸ hD
    · exact hE b hb
  let G := F.filter fun b => (region F b).Nonempty ∧ region F b ⊆ S
  refine ⟨F,G,hF,Finset.filter_subset _ _,?_,?_,?_,?_⟩
  · intro b hb
    exact (Finset.mem_filter.mp hb).2.1
  · exact (regions_disjoint hl hF).mono (Finset.filter_subset _ _)
  · ext x
    constructor
    · intro hx
      obtain ⟨b,hb,hxb⟩ := exists_region (Finset.mem_insert_self D E) (hSD hx)
      refine ⟨b,Finset.mem_filter.mpr ⟨hb,⟨x,hxb⟩,?_⟩,hxb⟩
      intro y hy
      exact (hES x y (fun c hc => region_agreement hl hF hb hxb hy c
        (Finset.mem_insert_of_mem hc))).mp hx
    · rintro ⟨b,hb,hxb⟩
      exact (Finset.mem_filter.mp hb).2.2 hxb
  · intro b _
    exact holes_disjoint hl hF b

end IntegrationInACVF.Section3.PuncturedDecomposition
