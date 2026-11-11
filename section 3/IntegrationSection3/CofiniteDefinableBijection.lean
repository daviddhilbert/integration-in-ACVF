module

public import IntegrationSection3.CofiniteDefinableInjection

@[expose] public section

/-! A definable bijection between two cofinite subsets of the same
algebraic-field definable set preserves the finite complement cardinality.
This is proved from finite patching and first-order finite-field transfer. -/

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.CofiniteDefinableBijection

theorem complements_card_eq {K ι : Type*} [Field K] [IsAlgClosed K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (X : Set (ι → K)) (F G : Finset (ι → K))
    (hF : (F : Set (ι → K)) ⊆ X) (hG : (G : Set (ι → K)) ⊆ X)
    (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ X \ F ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (hbij : Set.BijOn f (X \ F) (X \ G)) : F.card = G.card := by
  classical
  let g : (ι → K) → (ι → K) := fun y =>
    if hy : y ∈ X \ G then Classical.choose (hbij.2.2 hy) else 0
  have hg (y : ι → K) (hy : y ∈ X \ G) : g y ∈ X \ F ∧ f (g y) = y := by
    dsimp only [g]
    rw [dif_pos hy]
    exact Classical.choose_spec (hbij.2.2 hy)
  have hGraph : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ X \ G ∧ z ∘ Sum.inr = g (z ∘ Sum.inl)} := by
    convert hf.preimage_comp (Sum.swap : ι ⊕ ι → ι ⊕ ι) using 1
    ext z
    change (z ∘ Sum.inl ∈ X \ G ∧ z ∘ Sum.inr = g (z ∘ Sum.inl)) ↔
      (z ∘ Sum.inr ∈ X \ F ∧ z ∘ Sum.inl = f (z ∘ Sum.inr))
    constructor
    · rintro ⟨hy,he⟩
      rw [he]
      exact ⟨(hg _ hy).1,(hg _ hy).2.symm⟩
    · rintro ⟨hx,he⟩
      have hy : z ∘ Sum.inl ∈ X \ G := he.symm ▸ hbij.1 hx
      refine ⟨hy,?_⟩
      exact hbij.2.1 hx (hg _ hy).1 (he.symm.trans (hg _ hy).2.symm)
  have hgm : (X \ G).MapsTo g (X \ F) := fun y hy => (hg y hy).1
  have hgi : (X \ G).InjOn g := by
    intro x hx y hy he
    exact (hg x hx).2.symm.trans ((congrArg f he).trans (hg y hy).2)
  exact Nat.le_antisymm
    (CofiniteDefinableInjection.deficit_le C X G F hG hF g hGraph hgm hgi)
    (CofiniteDefinableInjection.deficit_le C X F G hF hG f hf hbij.1 hbij.2.1)

end IntegrationInACVF.Section3.CofiniteDefinableBijection
