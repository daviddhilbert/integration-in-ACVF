module

public import IntegrationSection3.MinimalBallSupport

@[expose] public section

/-! The strict-cut geometry for enlarging holes in a punctured ball.
Definability of the enlargement is a separate obligation; this module
supplies the nonempty proper-subset argument from laminar non-covering. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport

namespace IntegrationInACVF.Section3.PunctureCuts

variable {X : Type*} {balls : Set (Set X)}

theorem exists_avoiding (hl : IsLaminar balls) (hnf : AvoidsFiniteProperSubballs balls)
    {E : Set X} (hE : E ∈ balls) {F : Finset (Set X)} (hF : ∀ c ∈ F, c ∈ balls)
    (hnot : ∀ c ∈ F, ¬ E ⊆ c) : ∃ x ∈ E, ∀ c ∈ F, x ∉ c := by
  classical
  let G := F.filter fun c => c ⊂ E
  obtain ⟨x,hx,havoid⟩ := hnf E hE G (fun c hc =>
    ⟨hF c (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩)
  refine ⟨x,hx,fun c hc hxc => ?_⟩
  rcases hl E hE c (hF c hc) with hec | hce | hd
  · exact hnot c hc hec
  · have hs : c ⊂ E := ⟨hce,hnot c hc⟩
    exact havoid c (Finset.mem_filter.mpr ⟨hc,hs⟩) hxc
  · exact Set.disjoint_left.mp hd hx hxc

theorem not_subset_old_holes {F : Finset (Set X)}
    (hdis : (F : Set (Set X)).Pairwise Disjoint) {h E : Set X}
    (hh : h ∈ F) (hne : h.Nonempty) (hstrict : h ⊂ E) :
    ∀ c ∈ F, ¬ E ⊆ c := by
  intro c hc hEc
  by_cases he : c = h
  · rw [he] at hEc
    exact hstrict.2 hEc
  · obtain ⟨x,hx⟩ := hne
    exact Set.disjoint_left.mp (hdis hh hc (fun hh' => he hh'.symm)) hx (hEc (hstrict.1 hx))

theorem strict_replacement (hl : IsLaminar balls) (hnf : AvoidsFiniteProperSubballs balls)
    {P : Set X} (hP : P ∈ balls) {F G : Finset (Set X)}
    (hF : ∀ c ∈ F, c ∈ balls) (hG : ∀ c ∈ G, c ∈ balls ∧ c ⊂ P)
    (hcover : ∀ c ∈ F, ∃ d ∈ G, c ⊆ d)
    (hextra : ∃ E ∈ G, ∀ c ∈ F, ¬ E ⊆ c) :
    (P \ {x | ∃ c ∈ G, x ∈ c}).Nonempty ∧
      (P \ {x | ∃ c ∈ G, x ∈ c}) ⊂ (P \ {x | ∃ c ∈ F, x ∈ c}) := by
  obtain ⟨x,hx,havoid⟩ := hnf P hP G hG
  have hne : (P \ {x | ∃ c ∈ G, x ∈ c}).Nonempty :=
    ⟨x,hx,fun ⟨c,hc,hxc⟩ => havoid c hc hxc⟩
  have hsub : P \ {x | ∃ c ∈ G, x ∈ c} ⊆ P \ {x | ∃ c ∈ F, x ∈ c} := by
    rintro y ⟨hy,hn⟩
    refine ⟨hy,?_⟩
    rintro ⟨c,hc,hyc⟩
    obtain ⟨d,hd,hcd⟩ := hcover c hc
    exact hn ⟨d,hd,hcd hyc⟩
  refine ⟨hne,hsub,?_⟩
  intro hrev
  obtain ⟨E,hEG,hnot⟩ := hextra
  obtain ⟨y,hyE,hyF⟩ := exists_avoiding hl hnf (hG E hEG).1 hF hnot
  have hyold : y ∈ P \ {x | ∃ c ∈ F, x ∈ c} :=
    ⟨(hG E hEG).2.1 hyE,fun ⟨c,hc,hyc⟩ => hyF c hc hyc⟩
  exact (hrev hyold).2 ⟨E,hEG,hyE⟩

end IntegrationInACVF.Section3.PunctureCuts
