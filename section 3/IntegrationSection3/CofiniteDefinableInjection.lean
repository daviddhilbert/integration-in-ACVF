module

public import IntegrationSection3.FiniteDefinablePatching
public import Mathlib.Data.Set.Card

@[expose] public section

/-! An injective definable map cannot increase a finite deficit inside
the same algebraic-field definable set. The finite patch argument is
derived from the checked definable Dedekind-finiteness theorem. -/

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.CofiniteDefinableInjection

theorem deficit_le {K ι : Type*} [Field K] [IsAlgClosed K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (X : Set (ι → K)) (F G : Finset (ι → K))
    (hF : (F : Set (ι → K)) ⊆ X) (hG : (G : Set (ι → K)) ⊆ X)
    (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ X \ F ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (hm : (X \ F).MapsTo f (X \ G)) (hinj : (X \ F).InjOn f) : G.card ≤ F.card := by
  classical
  by_contra hbad
  have hFG : F.card ≤ G.card := Nat.le_of_lt (Nat.lt_of_not_ge hbad)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe] using hFG : Fintype.card F ≤ Fintype.card G)
  let g : (ι → K) → (ι → K) := fun x => if hx : x ∈ F then (e ⟨x,hx⟩).val else f x
  let P : Set (ι ⊕ ι → K) := Set.range (fun x : F => Sum.elim x.val (g x.val))
  have hP : (Set.univ : Set K).Definable Language.ring P :=
    FiniteDefinablePatching.finite_univ Language.ring (Set.finite_range _)
  have hPeq (z : ι ⊕ ι → K) : z ∈ P ↔ z ∘ Sum.inl ∈ F ∧ z ∘ Sum.inr = g (z ∘ Sum.inl) := by
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.property,rfl⟩
    · rintro ⟨hx,he⟩
      refine ⟨⟨z ∘ Sum.inl,hx⟩,?_⟩
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (congrFun he i).symm
  have hGraph : (Set.univ : Set K).Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ X ∧ z ∘ Sum.inr = g (z ∘ Sum.inl)} := by
    have hd := (hf.mono (Set.subset_univ C)).union hP
    convert hd using 1
    ext z
    rw [Set.mem_union,hPeq]
    change (z ∘ Sum.inl ∈ X ∧ z ∘ Sum.inr = g (z ∘ Sum.inl)) ↔
      ((z ∘ Sum.inl ∈ X ∧ z ∘ Sum.inl ∉ F) ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)) ∨
        (z ∘ Sum.inl ∈ F ∧ z ∘ Sum.inr = g (z ∘ Sum.inl))
    by_cases hz : z ∘ Sum.inl ∈ F
    · exact ⟨fun h => Or.inr ⟨hz,h.2⟩,fun h => h.elim
        (fun h => (h.1.2 hz).elim) (fun h => ⟨hF h.1,h.2⟩)⟩
    · have hg : g (z ∘ Sum.inl) = f (z ∘ Sum.inl) := dif_neg hz
      rw [hg]
      exact ⟨fun h => Or.inl ⟨⟨h.1,hz⟩,h.2⟩,fun h => h.elim
        (fun h => ⟨h.1.1,h.2⟩) (fun h => (hz h.1).elim)⟩
  have hgMap : X.MapsTo g X := by
    intro x hx
    by_cases hxF : x ∈ F
    · change (if h : x ∈ F then (e ⟨x,h⟩).val else f x) ∈ X
      rw [dif_pos hxF]
      exact hG (e ⟨x,hxF⟩).property
    · change (if h : x ∈ F then (e ⟨x,h⟩).val else f x) ∈ X
      rw [dif_neg hxF]
      exact (hm ⟨hx,hxF⟩).1
  have hgInj : X.InjOn g := by
    intro x hx y hy he
    by_cases hxF : x ∈ F <;> by_cases hyF : y ∈ F
    · have he' : e ⟨x,hxF⟩ = e ⟨y,hyF⟩ := Subtype.ext (by simpa only [g,dif_pos hxF,dif_pos hyF] using he)
      exact congrArg Subtype.val (e.injective he')
    · have hxG : g x ∈ G := by simpa only [g,dif_pos hxF] using (e ⟨x,hxF⟩).property
      have hyG : g y ∉ G := by simpa only [g,dif_neg hyF,Finset.mem_coe] using (hm ⟨hy,hyF⟩).2
      exact (hyG (he ▸ hxG)).elim
    · have hyG : g y ∈ G := by simpa only [g,dif_pos hyF] using (e ⟨y,hyF⟩).property
      have hxG : g x ∉ G := by simpa only [g,dif_neg hxF,Finset.mem_coe] using (hm ⟨hx,hxF⟩).2
      exact (hxG (he.symm ▸ hyG)).elim
    · exact hinj ⟨hx,hxF⟩ ⟨hy,hyF⟩ (by simpa only [g,dif_neg hxF,dif_neg hyF] using he)
  have hgSurj := ACFDefinableInjection.surjOn_of_injOn Set.univ X g hGraph hgMap hgInj
  have heSurj : Function.Surjective e := by
    intro y
    obtain ⟨x,hx,hgx⟩ := hgSurj (hG y.property)
    by_cases hxF : x ∈ F
    · exact ⟨⟨x,hxF⟩,Subtype.ext (by simpa only [g,dif_pos hxF] using hgx)⟩
    · have heq : f x = y.val := by simpa only [g,dif_neg hxF] using hgx
      exact ((hm ⟨hx,hxF⟩).2 (heq.symm ▸ y.property)).elim
  apply hbad
  simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective e heSurj

theorem finite_image_complement {K ι : Type*} [Field K] [IsAlgClosed K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (X : Set (ι → K)) (F : Finset (ι → K)) (hF : (F : Set (ι → K)) ⊆ X)
    (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ X \ F ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (hm : (X \ F).MapsTo f X) (hinj : (X \ F).InjOn f) :
    (X \ f '' (X \ F)).Finite ∧ (X \ f '' (X \ F)).ncard ≤ F.card := by
  classical
  let Y := X \ f '' (X \ F)
  have hCount (G : Finset (ι → K)) (hG : (G : Set (ι → K)) ⊆ Y) : G.card ≤ F.card := by
    apply deficit_le C X F G hF (fun _ hx => (hG hx).1) f hf _ hinj
    intro x hx
    refine ⟨hm hx,?_⟩
    intro hfx
    exact (hG hfx).2 ⟨x,hx,rfl⟩
  have hFinite : Y.Finite := by
    by_contra hn
    obtain ⟨Z,hZ,hZfin,hZcard⟩ := (show Y.Infinite from hn).exists_subset_ncard_eq (F.card+1)
    have hZG : (hZfin.toFinset : Set (ι → K)) ⊆ Y := by
      rw [hZfin.coe_toFinset]
      exact hZ
    have hc := hCount hZfin.toFinset hZG
    have hc' : hZfin.toFinset.card = F.card+1 := by
      rw [← Set.ncard_coe_finset,hZfin.coe_toFinset,hZcard]
    omega
  refine ⟨hFinite,?_⟩
  have hG : (hFinite.toFinset : Set (ι → K)) ⊆ Y := by rw [hFinite.coe_toFinset]
  change Y.ncard ≤ F.card
  rw [← hFinite.coe_toFinset,Set.ncard_coe_finset]
  exact hCount hFinite.toFinset hG

end IntegrationInACVF.Section3.CofiniteDefinableInjection
