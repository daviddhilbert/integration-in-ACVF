module

public import IntegrationSection3.DefinableInjectionSentence

@[expose] public section

/-! Definable Dedekind finiteness for algebraically closed fields.
The transfer argument adapts the checked Apache-2.0 Mathlib
FieldTheory/AxGrothendieck.lean: first prove the relation sentence over
algebraic closures of finite fields, then use completeness and the
characteristic-zero transfer theorem. No constructible-map input is assumed.
-/

open Set Classical FirstOrder FirstOrder.Language FirstOrder.Field FirstOrder.Ring
open IntegrationInACVF.Section3.DefinableInjectionSentence

namespace IntegrationInACVF.Section3.ACFDefinableInjection

theorem locally_finite_scheme {K F₀ α ι : Type*} [Field F₀] [Finite F₀]
    [Field K] [Algebra F₀ K] [Algebra.IsAlgebraic F₀ K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι] [Finite α]
    (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) : K ⊨ scheme φ := by
  apply (realize_scheme φ).mpr
  intro v hRight hLeft hNext w hw
  let R : Set (ι ⊕ ι → K) := {z | φ.Realize (Sum.elim v z)}
  have hR : (Set.univ : Set K).Definable Language.ring R := by
    apply Set.definable_iff_exists_formula_sum.mpr
    refine ⟨φ.relabel (Sum.map (fun a => (⟨v a,Set.mem_univ _⟩ : (Set.univ : Set K))) id),?_⟩
    ext z
    simp only [Formula.realize_relabel,Set.mem_ofPred_eq]
    change φ.Realize (Sum.elim v z) ↔ _
    apply iff_of_eq
    congr 1
    funext j
    cases j <;> rfl
  have hRU (x y z : ι → K) (hx : Sum.elim x y ∈ R) (hy : Sum.elim x z ∈ R) : y = z :=
    hRight (fun p => ![x p.2,y p.2,z p.2] p.1) hx hy
  have hLU (x y z : ι → K) (hx : Sum.elim x z ∈ R) (hy : Sum.elim y z ∈ R) : x = y :=
    hLeft (fun p => ![x p.2,y p.2,z p.2] p.1) hx hy
  have hN (x y : ι → K) (hx : Sum.elim x y ∈ R) : ∃ z, Sum.elim y z ∈ R :=
    hNext (fun p => ![x p.2,y p.2] p.1) hx
  exact LocallyFiniteRelations.every_input_has_predecessor (F₀ := F₀) Set.univ R hR hRU hLU hN
    (fun i => w (0,i)) (fun i => w (1,i)) hw

theorem models_scheme_prime {α ι : Type*} [Finite α] [Finite ι]
    {p : ℕ} (hp : p.Prime) (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) :
    Theory.ACF p ⊨ᵇ scheme φ := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := FirstOrder.Ring.compatibleRingOfRing (AlgebraicClosure (ZMod p))
  rw [← (ACF_isComplete (Or.inl hp)).realize_sentence_iff _ (AlgebraicClosure (ZMod p))]
  exact locally_finite_scheme (F₀ := ZMod p) φ

theorem models_scheme {α ι : Type*} [Finite α] [Finite ι]
    {p : ℕ} (hp : p.Prime ∨ p = 0) (φ : Language.ring.Formula (α ⊕ (ι ⊕ ι))) :
    Theory.ACF p ⊨ᵇ scheme φ := by
  rcases hp with hp | rfl
  · exact models_scheme_prime hp φ
  · rw [ACF_zero_realize_iff_infinite_ACF_prime_realize]
    convert Set.infinite_univ (α := Nat.Primes)
    rw [Set.eq_univ_iff_forall]
    intro ⟨p,hp⟩
    exact models_scheme_prime hp φ

theorem surjOn_of_injOn {K ι : Type*} [Field K] [IsAlgClosed K]
    [FirstOrder.Ring.CompatibleRing K] [Finite ι]
    (C : Set K) (S : Set (ι → K)) (f : (ι → K) → (ι → K))
    (hf : C.Definable Language.ring
      {z : ι ⊕ ι → K | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)})
    (hm : S.MapsTo f S) (hinj : S.InjOn f) : S.SurjOn f S := by
  classical
  obtain ⟨c,_,hc⟩ := Set.definable_iff_finitely_definable.mp hf
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hc
  let p := ringChar K
  have hp := CharP.char_is_prime_or_zero K p
  have h := models_scheme hp φ
  rw [← (ACF_isComplete hp).realize_sentence_iff _ K,realize_scheme] at h
  have hRel (x y : ι → K) :
      φ.Realize (Sum.elim (Subtype.val : c → K) (Sum.elim x y)) ↔ x ∈ S ∧ y = f x := by
    exact (Set.ext_iff.mp hφ (Sum.elim x y)).symm
  have hRight (w : Fin 3 × ι → K)
      (h1 : φ.Realize (Sum.elim (Subtype.val : c → K)
        (Sum.elim (fun i => w (0,i)) (fun i => w (1,i)))))
      (h2 : φ.Realize (Sum.elim (Subtype.val : c → K)
        (Sum.elim (fun i => w (0,i)) (fun i => w (2,i))))) :
      (fun i => w (1,i)) = (fun i => w (2,i)) :=
    ((hRel _ _).mp h1).2.trans ((hRel _ _).mp h2).2.symm
  have hLeft (w : Fin 3 × ι → K)
      (h1 : φ.Realize (Sum.elim (Subtype.val : c → K)
        (Sum.elim (fun i => w (0,i)) (fun i => w (2,i)))))
      (h2 : φ.Realize (Sum.elim (Subtype.val : c → K)
        (Sum.elim (fun i => w (1,i)) (fun i => w (2,i))))) :
      (fun i => w (0,i)) = (fun i => w (1,i)) := by
    obtain ⟨h0,he0⟩ := (hRel _ _).mp h1
    obtain ⟨h1,he1⟩ := (hRel _ _).mp h2
    exact hinj h0 h1 (he0.symm.trans he1)
  have hNext (w : Fin 2 × ι → K)
      (h1 : φ.Realize (Sum.elim (Subtype.val : c → K)
        (Sum.elim (fun i => w (0,i)) (fun i => w (1,i))))) :
      ∃ z : ι → K, φ.Realize (Sum.elim (Subtype.val : c → K) (Sum.elim (fun i => w (1,i)) z)) := by
    obtain ⟨hx,he⟩ := (hRel _ _).mp h1
    refine ⟨f (fun i => w (1,i)),(hRel _ _).mpr ⟨?_,rfl⟩⟩
    exact he.symm ▸ hm hx
  have hPrev := h Subtype.val hRight hLeft hNext
  intro y hy
  have hY := (hRel y (f y)).mpr ⟨hy,rfl⟩
  obtain ⟨x,hx⟩ := hPrev (fun p => ![y p.2,f y p.2] p.1) hY
  obtain ⟨hxS,he⟩ := (hRel x y).mp hx
  exact ⟨x,hxS,he.symm⟩

end IntegrationInACVF.Section3.ACFDefinableInjection
