module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Function

@[expose] public section

/-! A bijection matching infinite classes up to finite exceptions induces
an actual bijection of their indices. Existence of a match on both sides
is explicit; no surjectivity conclusion is drawn from a bound on exceptions. -/

open Set Classical

namespace IntegrationInACVF.Section3.CofiniteClassMatching

variable {X Y I J : Type*}

def Matches (C : I → Set X) (D : J → Set Y) (f : X → Y) (i : I) (j : J) : Prop :=
  (C i \ f ⁻¹' D j).Finite ∧ (D j \ f '' C i).Finite

theorem row_unique (C : I → Set X) (D : J → Set Y) (f : X → Y)
    (hC : ∀ i, (C i).Infinite) (hD : Pairwise (fun j k => Disjoint (D j) (D k)))
    {i : I} {j k : J} (hj : Matches C D f i j) (hk : Matches C D f i k) : j = k := by
  by_contra hne
  obtain ⟨x,hxC,hxBad⟩ := ((hC i).sdiff (hj.1.union hk.1)).nonempty
  have hxj : f x ∈ D j := by
    by_contra h
    exact hxBad (Or.inl ⟨hxC,h⟩)
  have hxk : f x ∈ D k := by
    by_contra h
    exact hxBad (Or.inr ⟨hxC,h⟩)
  exact Set.disjoint_left.mp (hD hne) hxj hxk

theorem column_unique (C : I → Set X) (D : J → Set Y) (f : X → Y) (A : Set X)
    (hSub : ∀ i, C i ⊆ A) (hInj : Set.InjOn f A)
    (hC : Pairwise (fun i k => Disjoint (C i) (C k))) (hD : ∀ j, (D j).Infinite)
    {i k : I} {j : J} (hi : Matches C D f i j) (hk : Matches C D f k j) : i = k := by
  by_contra hne
  obtain ⟨y,hyD,hyBad⟩ := ((hD j).sdiff (hi.2.union hk.2)).nonempty
  have hyi : y ∈ f '' C i := by
    by_contra h
    exact hyBad (Or.inl ⟨hyD,h⟩)
  have hyk : y ∈ f '' C k := by
    by_contra h
    exact hyBad (Or.inr ⟨hyD,h⟩)
  obtain ⟨x,hx,hfx⟩ := hyi
  obtain ⟨z,hz,hfz⟩ := hyk
  have hxz : x = z := hInj (hSub i hx) (hSub k hz) (hfx.trans hfz.symm)
  exact Set.disjoint_left.mp (hC hne) hx (hxz.symm ▸ hz)

theorem inverse_matches (C : I → Set X) (D : J → Set Y) (f : X → Y) (h : Y → X)
    (A : Set X) (B : Set Y) (hC : ∀ i, C i ⊆ A) (hD : ∀ j, D j ⊆ B)
    (hLeft : ∀ x ∈ A, h (f x) = x) (hRight : ∀ y ∈ B, f (h y) = y)
    {i : I} {j : J} (hMatch : Matches D C h j i) : Matches C D f i j := by
  have hFirst : C i \ f ⁻¹' D j = C i \ h '' D j := by
    ext x
    apply and_congr_right
    intro hx
    apply not_congr
    constructor
    · intro hfx
      exact ⟨f x,hfx,hLeft x (hC i hx)⟩
    · rintro ⟨y,hy,rfl⟩
      change f (h y) ∈ D j
      rw [hRight y (hD j hy)]
      exact hy
  have hSecond : D j \ f '' C i = D j \ h ⁻¹' C i := by
    ext y
    apply and_congr_right
    intro hy
    apply not_congr
    constructor
    · rintro ⟨x,hx,rfl⟩
      change h (f x) ∈ C i
      rw [hLeft x (hC i hx)]
      exact hx
    · intro hhy
      exact ⟨h y,hhy,hRight y (hD j hy)⟩
  exact ⟨hFirst.symm ▸ hMatch.2,hSecond.symm ▸ hMatch.1⟩

theorem exists_bijection (C : I → Set X) (D : J → Set Y) (f : X → Y) (A : Set X)
    (hSub : ∀ i, C i ⊆ A) (hInj : Set.InjOn f A)
    (hCInf : ∀ i, (C i).Infinite) (hDInf : ∀ j, (D j).Infinite)
    (hCDis : Pairwise (fun i k => Disjoint (C i) (C k)))
    (hDDis : Pairwise (fun j k => Disjoint (D j) (D k)))
    (hRow : ∀ i, ∃ j, Matches C D f i j) (hCol : ∀ j, ∃ i, Matches C D f i j) :
    ∃ e : I → J, Function.Bijective e ∧ ∀ i j, Matches C D f i j ↔ e i = j := by
  choose e he using hRow
  refine ⟨e,⟨?_,?_⟩,?_⟩
  · intro i k hik
    have hk : Matches C D f k (e i) := hik.symm ▸ he k
    exact column_unique C D f A hSub hInj hCDis hDInf (he i) hk
  · intro j
    obtain ⟨i,hij⟩ := hCol j
    exact ⟨i,row_unique C D f hCInf hDDis (he i) hij⟩
  · intro i j
    exact ⟨fun hij => row_unique C D f hCInf hDDis (he i) hij,fun hij => hij ▸ he i⟩

end IntegrationInACVF.Section3.CofiniteClassMatching
