module

public import IntegrationSection3.PuncturedDecomposition
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! Minimal finite supports in a laminar ball family. Uniqueness uses the
geometric non-covering property explicitly; the actual ACVF instance is
supplied separately. No definability or atomicity conclusion is assumed. -/

open Set

namespace IntegrationInACVF.Section3.MinimalBallSupport

variable {X : Type*}

def Supports (F : Finset (Set X)) (S : Set X) : Prop :=
  ∀ x y, (∀ b ∈ F, (x ∈ b ↔ y ∈ b)) → (x ∈ S ↔ y ∈ S)

def IsSupport (balls : Set (Set X)) (F : Finset (Set X)) (S : Set X) : Prop :=
  (∀ b ∈ F, b ∈ balls) ∧ Supports F S

def IsMinimalSupport (balls : Set (Set X)) (F : Finset (Set X)) (S : Set X) : Prop :=
  IsSupport balls F S ∧ ∀ G, IsSupport balls G S → F.card ≤ G.card

theorem exists_minimal_support {balls : Set (Set X)} {S : Set X}
    (hS : HasFiniteBallSupport balls S) : ∃ F, IsMinimalSupport balls F S := by
  classical
  have hn : ∃ n : ℕ, ∃ F : Finset (Set X), IsSupport balls F S ∧ F.card = n := by
    obtain ⟨F,hF,hFS⟩ := hS
    exact ⟨F.card,F,⟨hF,hFS⟩,rfl⟩
  obtain ⟨F,hF,hcard⟩ := Nat.find_spec hn
  refine ⟨F,hF,fun G hG => ?_⟩
  rw [hcard]
  exact Nat.find_min' hn ⟨G,hG,rfl⟩

theorem essential {balls : Set (Set X)} {F : Finset (Set X)} {S b : Set X}
    (hF : IsMinimalSupport balls F S) (hb : b ∈ F) :
    ∃ x y : X, (∀ c ∈ F.erase b, x ∈ c ↔ y ∈ c) ∧ ¬ (x ∈ S ↔ y ∈ S) := by
  classical
  by_contra hn
  have he : IsSupport balls (F.erase b) S := by
    refine ⟨fun c hc => hF.1.1 c (Finset.mem_erase.mp hc).2,?_⟩
    intro x y hxy
    by_contra hne
    exact hn ⟨x,y,hxy,hne⟩
  exact (not_le_of_gt (Finset.card_erase_lt_of_mem hb)) (hF.2 (F.erase b) he)


/-- No ball is covered by finitely many proper subballs. This is a geometric
property to be proved for ACVF, not an atomicity or definability hypothesis. -/
def AvoidsFiniteProperSubballs (balls : Set (Set X)) : Prop :=
  ∀ b ∈ balls, ∀ F : Finset (Set X),
    (∀ c ∈ F, c ∈ balls ∧ c ⊂ b) → ∃ x ∈ b, ∀ c ∈ F, x ∉ c

theorem region_mem_iff_subset {balls : Set (Set X)} (hl : IsLaminar balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls)
    {b c : Set X} (hb : b ∈ balls) {x : X}
    (hx : x ∈ PuncturedDecomposition.region F b) (hc : c ∈ F) :
    x ∈ c ↔ b ⊆ c := by
  constructor
  · intro hxc
    rcases hl b hb c (hF c hc) with hbc | hcb | hd
    · exact hbc
    · by_cases he : c = b
      · exact he ▸ Set.Subset.rfl
      · exact (hx.2 c hc (Set.ssubset_iff_subset_ne.mpr ⟨hcb,he⟩) hxc).elim
    · exact (Set.disjoint_left.mp hd hx.1 hxc).elim
  · intro hbc
    exact hbc hx.1

theorem strata_points {balls : Set (Set X)} (hl : IsLaminar balls)
    (htop : (Set.univ : Set X) ∈ balls) (hav : AvoidsFiniteProperSubballs balls)
    {F : Finset (Set X)} (hF : ∀ b ∈ F, b ∈ balls)
    {b : Set X} (hb : b ∈ F) (hbtop : b ≠ Set.univ) :
    ∃ x y : X, x ∈ b ∧ y ∉ b ∧ ∀ c ∈ F, c ≠ b → (x ∈ c ↔ y ∈ c) := by
  classical
  let I := F.filter fun c => c ⊂ b
  obtain ⟨x,hxb,hxn⟩ := hav b (hF b hb) I (by
    intro c hc
    exact ⟨hF c (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩)
  have hxr : x ∈ PuncturedDecomposition.region F b :=
    ⟨hxb,fun c hc hcb => hxn c (Finset.mem_filter.mpr ⟨hc,hcb⟩)⟩
  let H := (insert Set.univ F).filter fun c => b ⊂ c
  have hh : H.Nonempty :=
    ⟨Set.univ,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,
      Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _,hbtop⟩⟩⟩
  obtain ⟨U,hU,hmin⟩ := H.exists_minimal hh
  obtain ⟨hUF,hbU⟩ := Finset.mem_filter.mp hU
  have hUb : U ∈ balls := (Finset.mem_insert.mp hUF).elim (fun h => h.symm ▸ htop) (hF U)
  let J := F.filter fun c => c ⊂ U
  obtain ⟨y,hyU,hyn⟩ := hav U hUb J (by
    intro c hc
    exact ⟨hF c (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩)
  have hyr : y ∈ PuncturedDecomposition.region F U :=
    ⟨hyU,fun c hc hcU => hyn c (Finset.mem_filter.mpr ⟨hc,hcU⟩)⟩
  have hyb : y ∉ b := hyn b (Finset.mem_filter.mpr ⟨hb,hbU⟩)
  refine ⟨x,y,hxb,hyb,?_⟩
  intro c hc hcb
  have he : b ⊆ c ↔ U ⊆ c := by
    constructor
    · intro hbc
      have hcH : c ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hc,
        Set.ssubset_iff_subset_ne.mpr ⟨hbc,hcb.symm⟩⟩
      rcases hl U hUb c (hF c hc) with hUc | hcU | hd
      · exact hUc
      · exact hmin hcH hcU
      · exact (Set.disjoint_left.mp hd (hbU.1 hxb) (hbc hxb)).elim
    · exact fun hUc => hbU.1.trans hUc
  exact (region_mem_iff_subset hl hF (hF b hb) hxr hc).trans
    (he.trans (region_mem_iff_subset hl hF hUb hyr hc).symm)

theorem essential_ne_univ {balls : Set (Set X)} {F : Finset (Set X)} {S b : Set X}
    (hF : IsMinimalSupport balls F S) (hb : b ∈ F) : b ≠ Set.univ := by
  classical
  intro he
  obtain ⟨x,y,hxy,hne⟩ := essential hF hb
  apply hne
  apply hF.1.2 x y
  intro c hc
  by_cases hcb : c = b
  · rw [hcb,he]
    exact iff_of_true (Set.mem_univ _) (Set.mem_univ _)
  · exact hxy c (Finset.mem_erase.mpr ⟨hcb,hc⟩)

theorem region_of_agreement {F : Finset (Set X)} {b : Set X} {x y : X}
    (hx : x ∈ b) (hy : y ∉ b)
    (hxy : ∀ c ∈ F, c ≠ b → (x ∈ c ↔ y ∈ c)) :
    x ∈ PuncturedDecomposition.region F b := by
  refine ⟨hx,?_⟩
  intro c hc hcb hxc
  exact hy (hcb.1 ((hxy c hc ((Set.ssubset_iff_subset_ne.mp hcb).2)).mp hxc))

theorem minimal_subset_support {balls : Set (Set X)} (hl : IsLaminar balls)
    (htop : (Set.univ : Set X) ∈ balls) (hav : AvoidsFiniteProperSubballs balls)
    {F G : Finset (Set X)} {S : Set X}
    (hF : IsMinimalSupport balls F S) (hG : IsSupport balls G S) : F ⊆ G := by
  classical
  intro b hb
  by_contra hbg
  have hFG : ∀ c ∈ F ∪ G, c ∈ balls := by
    intro c hc
    exact (Finset.mem_union.mp hc).elim (hF.1.1 c) (hG.1 c)
  obtain ⟨x,y,hxb,hyb,hxy⟩ := strata_points hl htop hav hFG
    (Finset.mem_union_left G hb) (essential_ne_univ hF hb)
  have hxyF : ∀ c ∈ F, c ≠ b → (x ∈ c ↔ y ∈ c) :=
    fun c hc => hxy c (Finset.mem_union_left G hc)
  have hxr := region_of_agreement hxb hyb hxyF
  have hGxy : x ∈ S ↔ y ∈ S := hG.2 x y (fun c hc =>
    hxy c (Finset.mem_union_right F hc) (fun he => hbg (he ▸ hc)))
  have hcontra (u v : X) (hub : u ∈ b) (hvb : v ∉ b)
      (huv : ∀ c ∈ F.erase b, u ∈ c ↔ v ∈ c)
      (hne : ¬ (u ∈ S ↔ v ∈ S)) : False := by
    have hur := region_of_agreement hub hvb (fun c hc hcb => huv c (Finset.mem_erase.mpr ⟨hcb,hc⟩))
    have hux := PuncturedDecomposition.region_agreement hl hF.1.1 hb hur hxr
    have hUS : u ∈ S ↔ x ∈ S := hF.1.2 u x hux
    have hVS : v ∈ S ↔ y ∈ S := hF.1.2 v y (by
      intro c hc
      by_cases hcb : c = b
      · rw [hcb]
        exact iff_of_false hvb hyb
      · exact (huv c (Finset.mem_erase.mpr ⟨hcb,hc⟩)).symm.trans
          ((hux c hc).trans (hxyF c hc hcb)))
    exact hne (hUS.trans (hGxy.trans hVS.symm))
  obtain ⟨u,v,huv,hne⟩ := essential hF hb
  have hbneq : ¬ (u ∈ b ↔ v ∈ b) := by
    intro he
    apply hne
    apply hF.1.2 u v
    intro c hc
    by_cases hcb : c = b
    · exact hcb.symm ▸ he
    · exact huv c (Finset.mem_erase.mpr ⟨hcb,hc⟩)
  by_cases hub : u ∈ b
  · exact hcontra u v hub (fun hvb => hbneq (iff_of_true hub hvb)) huv hne
  · have hvb : v ∈ b := by
      by_contra hn
      exact hbneq (iff_of_false hub hn)
    exact hcontra v u hvb hub (fun c hc => (huv c hc).symm) (fun he => hne he.symm)

theorem minimal_unique {balls : Set (Set X)} (hl : IsLaminar balls)
    (htop : (Set.univ : Set X) ∈ balls) (hav : AvoidsFiniteProperSubballs balls)
    {F G : Finset (Set X)} {S : Set X}
    (hF : IsMinimalSupport balls F S) (hG : IsMinimalSupport balls G S) : F = G :=
  Finset.Subset.antisymm (minimal_subset_support hl htop hav hF hG.1)
    (minimal_subset_support hl htop hav hG hF.1)

end IntegrationInACVF.Section3.MinimalBallSupport
