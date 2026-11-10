module

public import IntegrationSection3.MinimalBallSupport

@[expose] public section

/-! The exact canonical support of one punctured ball. Every disjoint
proper hole and its parent is essential. In particular the parent is the
sole positive member, without assuming its original-base definability. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport
open IntegrationInACVF.Section3.PuncturedDecomposition

namespace IntegrationInACVF.Section3.PuncturedSupport

variable {X J : Type*} {balls : Set (Set X)}

theorem supports {P : Set X} (hP : P ∈ balls) {H : Finset (Set X)}
    (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ P) :
    IsSupport balls (insert P H) (P \ {x | ∃ h ∈ H, x ∈ h}) := by
  classical
  refine ⟨?_,?_⟩
  · intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · exact he.symm ▸ hP
    · exact (hH b hb).1
  · intro x y hxy
    have hp := hxy P (Finset.mem_insert_self _ _)
    constructor
    · rintro ⟨hxP,hnx⟩
      refine ⟨hp.mp hxP,?_⟩
      rintro ⟨h,hh,hyh⟩
      exact hnx ⟨h,hh,(hxy h (Finset.mem_insert_of_mem hh)).mpr hyh⟩
    · rintro ⟨hyP,hny⟩
      refine ⟨hp.mpr hyP,?_⟩
      rintro ⟨h,hh,hxh⟩
      exact hny ⟨h,hh,(hxy h (Finset.mem_insert_of_mem hh)).mp hxh⟩

theorem region_parent {P : Set X} {H : Finset (Set X)} (hH : ∀ h ∈ H, h ⊂ P) :
    region (insert P H) P = P \ {x | ∃ h ∈ H, x ∈ h} := by
  classical
  ext x
  constructor
  · rintro ⟨hxP,havoid⟩
    exact ⟨hxP,fun ⟨h,hh,hxh⟩ => havoid h (Finset.mem_insert_of_mem hh) (hH h hh) hxh⟩
  · rintro ⟨hxP,havoid⟩
    refine ⟨hxP,?_⟩
    intro h hh hproper hxh
    rcases Finset.mem_insert.mp hh with he | hh
    · rw [he] at hproper
      exact hproper.2 Set.Subset.rfl
    · exact havoid ⟨h,hh,hxh⟩

theorem minimal_eq (hl : IsLaminar balls) (htop : (Set.univ : Set X) ∈ balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P : Set X} (hP : P ∈ balls)
    (hout : ∃ y : X, y ∉ P) {H : Finset (Set X)}
    (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ P) (hdis : (H : Set (Set X)).Pairwise Disjoint)
    {G : Finset (Set X)} (hG : IsMinimalSupport balls G (P \ {x | ∃ h ∈ H, x ∈ h})) :
    G = insert P H := by
  classical
  have hGS := minimal_subset_support hl htop hnf hG (supports hP hH)
  obtain ⟨z,hzP,hzAway⟩ := hnf P hP H hH
  have hzBody : z ∈ P \ {x | ∃ h ∈ H, x ∈ h} :=
    ⟨hzP,fun ⟨h,hh,hzh⟩ => hzAway h hh hzh⟩
  have hPG : P ∈ G := by
    by_contra hnP
    obtain ⟨y,hyP⟩ := hout
    have hagree : ∀ c ∈ G, z ∈ c ↔ y ∈ c := by
      intro c hc
      rcases Finset.mem_insert.mp (hGS hc) with hcP | hcH
      · exact (hnP (hcP ▸ hc)).elim
      · exact iff_of_false (hzAway c hcH) (fun hyc => hyP ((hH c hcH).2.1 hyc))
    have hyBody := (hG.1.2 z y hagree).mp hzBody
    exact hyP hyBody.1
  have hHG : H ⊆ G := by
    intro h hh
    by_contra hnH
    obtain ⟨x,hxh,_⟩ := hnf h (hH h hh).1 ∅ (by simp)
    have hxP := (hH h hh).2.1 hxh
    have hagree : ∀ c ∈ G, x ∈ c ↔ z ∈ c := by
      intro c hc
      rcases Finset.mem_insert.mp (hGS hc) with hcP | hcH
      · rw [hcP]
        exact iff_of_true hxP hzP
      · by_cases hch : c = h
        · exact (hnH (hch ▸ hc)).elim
        · have hxc : x ∉ c := fun hx => Set.disjoint_left.mp
            (hdis hh hcH (fun he => hch he.symm)) hxh hx
          exact iff_of_false hxc (hzAway c hcH)
    have hxBody := (hG.1.2 x z hagree).mpr hzBody
    exact hxBody.2 ⟨h,hh,hxh⟩
  apply Finset.Subset.antisymm hGS
  intro c hc
  rcases Finset.mem_insert.mp hc with he | hc
  · exact he.symm ▸ hPG
  · exact hHG hc

theorem positive_names_singleton (hl : IsLaminar balls) (htop : (Set.univ : Set X) ∈ balls)
    (hnf : AvoidsFiniteProperSubballs balls) {P : Set X} (hP : P ∈ balls)
    (hout : ∃ y : X, y ∉ P) {H : Finset (Set X)}
    (hH : ∀ h ∈ H, h ∈ balls ∧ h ⊂ P) (hdis : (H : Set (Set X)).Pairwise Disjoint)
    {G : Finset (Set X)} (hG : IsMinimalSupport balls G (P \ {x | ∃ h ∈ H, x ∈ h}))
    {U : J → Set X} (hinj : Function.Injective U) (i : J) (hi : U i = P) :
    {j | U j ∈ G ∧ (region G (U j)).Nonempty ∧
      region G (U j) ⊆ P \ {x | ∃ h ∈ H, x ∈ h}} = {i} := by
  classical
  rw [minimal_eq hl htop hnf hP hout hH hdis hG]
  have he := region_parent (fun h hh => (hH h hh).2)
  have hBodyne : (P \ {x | ∃ h ∈ H, x ∈ h}).Nonempty := by
    obtain ⟨x,hx,havoid⟩ := hnf P hP H hH
    exact ⟨x,hx,fun ⟨h,hh,hxh⟩ => havoid h hh hxh⟩
  ext j
  constructor
  · rintro ⟨hj,hjne,hjsub⟩
    rcases Finset.mem_insert.mp hj with hjP | hjH
    · exact hinj (hjP.trans hi.symm)
    · obtain ⟨x,hx⟩ := hjne
      exact ((hjsub hx).2 ⟨U j,hjH,hx.1⟩).elim
  · intro hji
    have hji' : j = i := hji
    rw [hji']
    change U i ∈ insert P H ∧ (region (insert P H) (U i)).Nonempty ∧
      region (insert P H) (U i) ⊆ P \ {x | ∃ h ∈ H, x ∈ h}
    rw [hi]
    exact ⟨Finset.mem_insert_self _ _,by rwa [he],he.subset⟩

end IntegrationInACVF.Section3.PuncturedSupport
