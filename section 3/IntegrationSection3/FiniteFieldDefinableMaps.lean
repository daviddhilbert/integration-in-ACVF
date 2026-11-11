module

public import Mathlib.FieldTheory.AxGrothendieck
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.ModelTheory.ElementaryMaps

@[expose] public section

/-! Definable maps preserve finite subfields containing their parameters.
Uses the checked Mathlib finite-field Frobenius and polynomial splitting
APIs; this is a supporting step towards the residue-field conservation
argument, not an assumed constructible-bijection conservation theorem. -/

open Set FirstOrder FirstOrder.Language Polynomial

namespace IntegrationInACVF.Section3.FiniteFieldDefinableMaps

theorem power_fixed_iff_range {F K : Type*} [Field F] [Fintype F]
    [Field K] [Algebra F K] (x : K) :
    x ^ Fintype.card F = x ↔ x ∈ (algebraMap F K).range := by
  have hNZ : (X ^ Fintype.card F - X : F[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hSplits : (X ^ Fintype.card F - X : F[X]).Splits := by
    rw [Polynomial.splits_iff_card_roots,FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
    simp only [← Finset.card_def,Finset.card_univ]
  constructor
  · intro hx
    apply hSplits.mem_range_of_isRoot hNZ
    simpa only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.eval₂_sub,
      Polynomial.eval₂_pow,Polynomial.eval₂_X,sub_eq_zero] using hx
  · rintro ⟨y,rfl⟩
    simpa only [map_pow] using congrArg (algebraMap F K) (FiniteField.pow_card y)

theorem definable_invariant {K ι : Type*} [Field K] [FirstOrder.Ring.CompatibleRing K]
    (C : Set K) {R : Set (ι → K)} (hR : C.Definable Language.ring R)
    (σ : K ≃+* K) (hσ : ∀ c ∈ C, σ c = c) (w : ι → K) :
    σ ∘ w ∈ R ↔ w ∈ R := by
  obtain ⟨φ,rfl⟩ := Set.definable_iff_exists_formula_sum.mp hR
  let g : Language.ring.Equiv K K := FirstOrder.Ring.languageEquivEquivRingEquiv.symm σ
  have he : g ∘ Sum.elim (Subtype.val : C → K) w =
      Sum.elim (Subtype.val : C → K) (σ ∘ w) := by
    funext i
    cases i with
    | inl c => exact hσ c.val c.property
    | inr i => rfl
  have h := FirstOrder.Language.StrongHomClass.realize_formula g φ
    (v := Sum.elim (Subtype.val : C → K) w)
  rw [he] at h
  exact h

theorem mapsTo_finite_subfield {F K ι : Type*} [Field F] [Fintype F]
    [Field K] [Algebra F K] [Algebra.IsAlgebraic F K]
    [FirstOrder.Ring.CompatibleRing K]
    (C : Set K) (hC : C ⊆ (algebraMap F K).range)
    (S : Set (ι → K)) (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (x : ι → K) (hx : x ∈ S) (hxF : ∀ i, x i ∈ (algebraMap F K).range) :
    ∀ i, f x i ∈ (algebraMap F K).range := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F K
  have hfix (a : K) (ha : a ∈ (algebraMap F K).range) : σ a = a := by
    change a ^ Fintype.card F = a
    exact (power_fixed_iff_range a).mpr ha
  have hxEq : σ ∘ x = x := funext (fun i => hfix (x i) (hxF i))
  have hGraph : Sum.elim x (f x) ∈
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)} := ⟨hx,rfl⟩
  have h := (definable_invariant C hf σ.toRingEquiv
    (fun c hc => hfix c (hC hc)) (Sum.elim x (f x))).mpr hGraph
  change σ ∘ x ∈ S ∧ σ ∘ f x = f (σ ∘ x) at h
  rw [hxEq] at h
  intro i
  apply (power_fixed_iff_range (f x i)).mp
  exact congrFun h.2 i

end IntegrationInACVF.Section3.FiniteFieldDefinableMaps
