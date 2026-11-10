module

public import IntegrationSection3.CoarsePartition
public import Mathlib.Data.Set.Card

@[expose] public section

/-! A bounded finite relation cannot have infinitely many disjoint target
pieces whose inverse images all miss only finitely many proper source balls.
The finite row bound is explicit; no saturation property is defined here. -/

open Set
open IntegrationInACVF.Section3.MinimalBallSupport
open IntegrationInACVF.Section3.CoarsePartition

namespace IntegrationInACVF.Section3.CoarseRelationFibres

variable {X Y J : Type*} {balls : Set (Set X)}

/-- Infinite target pieces have infinite inverse images under a relation
with finite rows and surjective second projection onto that piece. -/
theorem infinite_preimage (R : X → Y → Prop) {P : Set X} {C : Set Y}
    (hC : C.Infinite) (hrow : ∀ x ∈ P, {y | R x y}.Finite)
    (hsurj : ∀ y ∈ C, ∃ x ∈ P, R x y) :
    {x | x ∈ P ∧ ∃ y ∈ C, R x y}.Infinite := by
  intro hfin
  have hf := hfin.biUnion (fun x hx => hrow x hx.1)
  apply hC
  apply hf.subset
  intro y hy
  obtain ⟨x,hx,hxy⟩ := hsurj y hy
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨⟨hx,y,hy,hxy⟩,hxy⟩⟩

theorem finite_intersection (hnf : AvoidsFiniteProperSubballs balls)
    {P : Set X} (hP : P ∈ balls) {S : J → Set X} (F : Finset J)
    (hS : ∀ j ∈ F, SmallIn balls P (P \ S j)) :
    ∃ x ∈ P, ∀ j ∈ F, x ∈ S j := by
  classical
  choose H hH hcov using fun j : F => hS j.val j.property
  let G := Finset.univ.biUnion H
  have hG : ∀ b ∈ G, b ∈ balls ∧ b ⊂ P := by
    intro b hb
    obtain ⟨j,_,hb⟩ := Finset.mem_biUnion.mp hb
    exact hH j b hb
  obtain ⟨x,hx,havoid⟩ := hnf P hP G hG
  refine ⟨x,hx,?_⟩
  intro j hj
  by_contra hxj
  obtain ⟨b,hb,hxb⟩ := hcov ⟨j,hj⟩ ⟨hx,hxj⟩
  exact havoid b (Finset.mem_biUnion.mpr ⟨⟨j,hj⟩,Finset.mem_univ _,hb⟩) hxb

theorem finite_family_bound (hnf : AvoidsFiniteProperSubballs balls)
    {P : Set X} (hP : P ∈ balls) (R : X → Y → Prop) (C : J → Set Y)
    {T : Set J} (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (N : ℕ) (hfinite : ∀ x ∈ P, {y | R x y}.Finite)
    (hbound : ∀ x ∈ P, {y | R x y}.ncard ≤ N)
    (F : Finset J) (hFT : (F : Set J) ⊆ T)
    (hcoarse : ∀ j ∈ F, SmallIn balls P (P \ {x | ∃ y ∈ C j, R x y})) : F.card ≤ N := by
  classical
  obtain ⟨x,hx,hall⟩ := finite_intersection hnf hP F hcoarse
  choose y hy hRy using fun j : F => hall j.val j.property
  have hinj : Function.Injective y := by
    intro j k he
    apply Subtype.ext
    by_contra hjk
    exact Set.disjoint_left.mp (hdis (hFT j.property) (hFT k.property) hjk)
      (hy j) (he.symm ▸ hy k)
  have hf := hfinite x hx
  have hsub : Finset.univ.image y ⊆ hf.toFinset := by
    intro z hz
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    exact hf.mem_toFinset.mpr (hRy j)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe,
    ← Set.ncard_eq_toFinset_card _ hf] at hcard
  exact hcard.trans (hbound x hx)

theorem coarse_indices_finite (hnf : AvoidsFiniteProperSubballs balls)
    {P : Set X} (hP : P ∈ balls) (R : X → Y → Prop) (C : J → Set Y)
    {T : Set J} (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (N : ℕ) (hfinite : ∀ x ∈ P, {y | R x y}.Finite)
    (hbound : ∀ x ∈ P, {y | R x y}.ncard ≤ N)
    (hcoarse : ∀ j ∈ T, SmallIn balls P (P \ {x | ∃ y ∈ C j, R x y})) : T.Finite := by
  classical
  by_contra hn
  have ht : T.Infinite := hn
  obtain ⟨F,hFT,hcard⟩ := ht.exists_subset_card_eq (N+1)
  have hle := finite_family_bound hnf hP R C hdis N hfinite hbound F hFT
    (fun j hj => hcoarse j (hFT hj))
  rw [hcard] at hle
  exact Nat.not_succ_le_self N hle

end IntegrationInACVF.Section3.CoarseRelationFibres
