module

public import IntegrationSection3.TaggedLineMaps
public import IntegrationSection3.CofiniteDefinableBijection

@[expose] public section

/-! Definable bijections between cofinite finite disjoint unions of affine
lines preserve both the number of lines and the number of deleted points.
The actual field tags, complete graph and finite deletion sets are explicit.
-/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open IntegrationInACVF.Section3.TaggedLineMaps

namespace IntegrationInACVF.Section3.TaggedCofiniteConservation

variable {K : Type*} [Field K] [IsAlgClosed K] [FirstOrder.Ring.CompatibleRing K]

theorem components_le (C : Set K) (P Q : Finset K) (F : Finset (Fin 2 → K))
    (hF : (F : Set (Fin 2 → K)) ⊆ space P) (f : (Fin 2 → K) → (Fin 2 → K))
    (hf : C.Definable Language.ring (FiniteTupleGraphs.graph (space P \ F) f))
    (hm : (space P \ F).MapsTo f (space Q)) (hinj : (space P \ F).InjOn f) : P.card ≤ Q.card := by
  by_contra hbad
  have hQP : Q.card ≤ P.card := Nat.le_of_lt (Nat.lt_of_not_ge hbad)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe] using hQP : Fintype.card Q ≤ Fintype.card P)
  have hNot : ¬ Function.Surjective e := by
    intro hSurj
    apply hbad
    simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective e hSurj
  obtain ⟨p,hp⟩ := not_forall.mp hNot
  let g := transport e ∘ f
  have hGraph := FiniteTupleGraphs.comp Language.ring Set.univ f (transport e)
    (hf.mono (Set.subset_univ C)) (TaggedLineMaps.graph_definable e) hm
  have hMap : (space P \ F).MapsTo g (space P) := fun x hx => TaggedLineMaps.mapsTo e (hm hx)
  have hInj : (space P \ F).InjOn g := by
    intro x hx y hy he
    exact hinj hx hy (TaggedLineMaps.injOn e (hm hx) (hm hy) he)
  have hFinite := (CofiniteDefinableInjection.finite_image_complement Set.univ
    (space P) F hF g hGraph hMap hInj).1
  have hInf := TaggedLineMaps.missing_line_infinite e p hp
  apply hInf
  apply hFinite.subset
  rintro y ⟨hy,hn⟩
  refine ⟨hy,?_⟩
  rintro ⟨x,hx,he⟩
  exact hn ⟨f x,hm hx,he⟩

theorem components_and_holes (C : Set K) (P Q : Finset K)
    (F G : Finset (Fin 2 → K)) (hF : (F : Set (Fin 2 → K)) ⊆ space P)
    (hG : (G : Set (Fin 2 → K)) ⊆ space Q)
    (f : (Fin 2 → K) → (Fin 2 → K))
    (hf : C.Definable Language.ring (FiniteTupleGraphs.graph (space P \ F) f))
    (hbij : Set.BijOn f (space P \ F) (space Q \ G)) : P.card = Q.card ∧ F.card = G.card := by
  classical
  letI : Inhabited K := ⟨0⟩
  have hPQ := components_le C P Q F hF f hf (fun x hx => (hbij.1 hx).1) hbij.2.1
  obtain ⟨g,hg,hgbij,_,_⟩ := FiniteTupleGraphs.inverse Language.ring C f hf hbij
  have hQP := components_le C Q P G hG g hg (fun x hx => (hgbij.1 hx).1) hgbij.2.1
  have hCard : P.card = Q.card := Nat.le_antisymm hPQ hQP
  let e : Q ≃ P := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hCard.symm)
  let t := transport e.toEmbedding
  have htMap := TaggedLineMaps.mapsTo e.toEmbedding
  have htInj := TaggedLineMaps.injOn e.toEmbedding
  have htSurj := TaggedLineMaps.surjOn e.toEmbedding e.surjective
  let G' := G.image t
  have hG' : (G' : Set (Fin 2 → K)) ⊆ space P := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact htMap (hG hx)
  have hCardG : G'.card = G.card := Finset.card_image_iff.mpr
    (fun x hx y hy he => htInj (hG hx) (hG hy) he)
  let h := t ∘ f
  have hGraph := FiniteTupleGraphs.comp Language.ring Set.univ f t
    (hf.mono (Set.subset_univ C)) (TaggedLineMaps.graph_definable e.toEmbedding)
    (fun x hx => (hbij.1 hx).1)
  have hBij : Set.BijOn h (space P \ F) (space P \ G') := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      have hfx := hbij.1 hx
      refine ⟨htMap hfx.1,?_⟩
      intro hy
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hy
      have hzf : z = f x := htInj (hG hz) hfx.1 he
      exact hfx.2 (hzf ▸ hz)
    · intro x hx y hy he
      exact hbij.2.1 hx hy (htInj (hbij.1 hx).1 (hbij.1 hy).1 he)
    · intro y hy
      obtain ⟨z,hz,he⟩ := htSurj hy.1
      have hzG : z ∉ G := fun hzG => hy.2 (Finset.mem_image.mpr ⟨z,hzG,he⟩)
      obtain ⟨x,hx,hfx⟩ := hbij.2.2 ⟨hz,hzG⟩
      refine ⟨x,hx,?_⟩
      change t (f x) = y
      rw [hfx]
      exact he
  have hHoles := CofiniteDefinableBijection.complements_card_eq Set.univ
    (space P) F G' hF hG' h hGraph hBij
  exact ⟨hCard,hHoles.trans hCardG⟩

end IntegrationInACVF.Section3.TaggedCofiniteConservation
