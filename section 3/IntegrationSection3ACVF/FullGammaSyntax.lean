import IntegrationSection3ACVF.FullBaseDefinability

/-!
# Gamma predicates over the combined interpreted base

The decoder and guards are the unchanged predecessor GammaSyntax. The
logical proofs adapt its Section4/GammaPredicates.lean to the proved
finite-support operations over the original real/Gamma/ball base.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def Definable (B : FullBaseAtomicity.Base (M := M)) {ι : Type} [Finite ι]
    (P : (ι → Values.Gamma (M := M)) → Prop) : Prop :=
  FullBaseAtomicity.OverBase B {a | GammaSyntax.Proper a ∧ P (GammaSyntax.decode a)}

def Scalar (B : FullBaseAtomicity.Base (M := M)) (A : Set (Values.Gamma (M := M))) : Prop :=
  FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Values.gammaPullback A}

variable {ι υ : Type} [Finite ι] [Finite υ] {B : FullBaseAtomicity.Base (M := M)}

theorem proper_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {a : ι → M | GammaSyntax.Proper a} :=
  FullBaseAtomicity.OverBase.of_real (B := B) (GammaSyntax.proper_definable B.real)

theorem Definable.of_real {P : (ι → Values.Gamma (M := M)) → Prop}
    (hP : GammaSyntax.Definable B.real P) : Definable B P :=
  FullBaseAtomicity.OverBase.of_real (B := B) hP

theorem Scalar.of_real {A : Set (Values.Gamma (M := M))}
    (hA : Values.GammaDefinable B.real A) : Scalar B A :=
  FullBaseAtomicity.OverBase.of_real (B := B)
    (((@definableAt_iff_normalized_raw M sM hM B.real .rv _).mp hA).1)

theorem Definable.true_ (B : FullBaseAtomicity.Base (M := M)) :
    Definable B (fun _ : ι → Values.Gamma (M := M) => True) := by
  simpa only [Definable,and_true] using proper_definable (ι := ι) B

theorem Definable.congr {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (h : ∀ a, P a ↔ Q a) : Definable B Q := by
  have he : P = Q := funext (fun a => propext (h a))
  rwa [← he]

theorem Definable.and {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (hQ : Definable B Q) : Definable B (fun a => P a ∧ Q a) := by
  change FullBaseAtomicity.OverBase B _
  convert FullBaseAtomicity.OverBase.inter hP hQ using 1
  ext a
  change (GammaSyntax.Proper a ∧ P (GammaSyntax.decode a) ∧ Q (GammaSyntax.decode a)) ↔
    ((GammaSyntax.Proper a ∧ P (GammaSyntax.decode a)) ∧
      GammaSyntax.Proper a ∧ Q (GammaSyntax.decode a))
  tauto

theorem Definable.not {P : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) : Definable B (fun a => ¬ P a) := by
  change FullBaseAtomicity.OverBase B _
  convert FullBaseAtomicity.OverBase.inter (proper_definable (ι := ι) B)
    (FullBaseAtomicity.OverBase.compl hP) using 1
  ext a
  change (GammaSyntax.Proper a ∧ ¬ P (GammaSyntax.decode a)) ↔
    (GammaSyntax.Proper a ∧ ¬ (GammaSyntax.Proper a ∧ P (GammaSyntax.decode a)))
  tauto

theorem Definable.or {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (hQ : Definable B Q) : Definable B (fun a => P a ∨ Q a) := by
  change FullBaseAtomicity.OverBase B _
  convert FullBaseAtomicity.OverBase.union hP hQ using 1
  ext a
  change (GammaSyntax.Proper a ∧ (P (GammaSyntax.decode a) ∨ Q (GammaSyntax.decode a))) ↔
    ((GammaSyntax.Proper a ∧ P (GammaSyntax.decode a)) ∨
      (GammaSyntax.Proper a ∧ Q (GammaSyntax.decode a)))
  tauto

theorem Definable.imp {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (hQ : Definable B Q) : Definable B (fun a => P a → Q a) := by
  simpa only [imp_iff_not_or] using hP.not.or hQ

theorem Definable.iff {P Q : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (hQ : Definable B Q) : Definable B (fun a => P a ↔ Q a) := by
  simpa only [iff_def] using (hP.imp hQ).and (hQ.imp hP)

theorem Definable.forall_finite {τ : Type} [Finite τ]
    {P : τ → (ι → Values.Gamma (M := M)) → Prop} (hP : ∀ t, Definable B (P t)) :
    Definable B (fun a => ∀ t, P t a) := by
  have hall : FullBaseAtomicity.OverBase B
      {a : ι → M | ∀ t, GammaSyntax.Proper a ∧ P t (GammaSyntax.decode a)} :=
    FullBaseAtomicity.OverBase.forall_finite hP
  change FullBaseAtomicity.OverBase B _
  convert FullBaseAtomicity.OverBase.inter (proper_definable (ι := ι) B) hall using 1
  ext a
  change (GammaSyntax.Proper a ∧ ∀ t, P t (GammaSyntax.decode a)) ↔
    (GammaSyntax.Proper a ∧ ∀ t, GammaSyntax.Proper a ∧ P t (GammaSyntax.decode a))
  exact ⟨fun h => ⟨h.1,fun t => ⟨h.1,h.2 t⟩⟩,fun h => ⟨h.1,fun t => (h.2 t).2⟩⟩

theorem Definable.reindex {P : (ι → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) (f : ι → υ) : Definable B (fun a => P (a ∘ f)) := by
  have h := FullBaseAtomicity.OverBase.inter (proper_definable (ι := υ) B)
    (FullBaseAtomicity.OverBase.preimage_comp hP f)
  change FullBaseAtomicity.OverBase B _
  convert h using 1
  ext a
  change (GammaSyntax.Proper a ∧ P (GammaSyntax.decode a ∘ f)) ↔
    (GammaSyntax.Proper a ∧ GammaSyntax.Proper (a ∘ f) ∧ P (GammaSyntax.decode (a ∘ f)))
  have he : GammaSyntax.decode (a ∘ f) = GammaSyntax.decode a ∘ f := rfl
  rw [he]
  exact ⟨fun h => ⟨h.1,fun j => h.1 (f j),h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

theorem Definable.exists_block {P : (ι ⊕ υ → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) :
    Definable B (fun a => ∃ b : υ → Values.Gamma (M := M), P (Sum.elim a b)) := by
  have h := FullBaseAtomicity.OverBase.exists_block hP
  change FullBaseAtomicity.OverBase B _
  convert h using 1
  ext a
  change (GammaSyntax.Proper a ∧ ∃ b, P (Sum.elim (GammaSyntax.decode a) b)) ↔
    ∃ b : υ → M, GammaSyntax.Proper (Sum.elim a b) ∧ P (GammaSyntax.decode (Sum.elim a b))
  constructor
  · rintro ⟨ha,b,hb⟩
    choose c hc hcv using fun j => EndpointLogic.codeValue_surjective (b j)
    refine ⟨c,?_,?_⟩
    · intro j
      cases j with
      | inl j => exact ha j
      | inr j => exact hc j
    · have he : GammaSyntax.decode (Sum.elim a c) = Sum.elim (GammaSyntax.decode a) b := by
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact hcv j
      rwa [he]
  · rintro ⟨b,hab,hp⟩
    have he : GammaSyntax.decode (Sum.elim a b) =
        Sum.elim (GammaSyntax.decode a) (GammaSyntax.decode b) := by
      funext j
      cases j <;> rfl
    exact ⟨fun j => hab (Sum.inl j),GammaSyntax.decode b,he ▸ hp⟩

theorem Definable.forall_block {P : (ι ⊕ υ → Values.Gamma (M := M)) → Prop}
    (hP : Definable B P) :
    Definable B (fun a => ∀ b : υ → Values.Gamma (M := M), P (Sum.elim a b)) := by
  simpa only [not_exists,not_not] using hP.not.exists_block.not

theorem lt_definable (B : FullBaseAtomicity.Base (M := M)) (i j : ι) :
    Definable B (fun a : ι → Values.Gamma (M := M) => a i < a j) :=
  Definable.of_real (GammaSyntax.lt_definable B.real i j)

theorem eq_definable (B : FullBaseAtomicity.Base (M := M)) (i j : ι) :
    Definable B (fun a : ι → Values.Gamma (M := M) => a i = a j) :=
  Definable.of_real (GammaSyntax.eq_definable B.real i j)

theorem mul_definable (B : FullBaseAtomicity.Base (M := M)) (i j k : ι) :
    Definable B (fun a : ι → Values.Gamma (M := M) => a i * a j = a k) :=
  Definable.of_real (GammaSyntax.mul_definable B.real i j k)

theorem scalar_definable_iff (A : Set (Values.Gamma (M := M))) :
    Definable B (fun a : Fin 1 → Values.Gamma (M := M) => a 0 ∈ A) ↔ Scalar B A := by
  have he : {a : Fin 1 → M | GammaSyntax.Proper a ∧ GammaSyntax.decode a 0 ∈ A} =
      {a | a 0 ∈ Values.gammaPullback A} := by
    ext a
    change (GammaSyntax.Proper a ∧ GammaSyntax.decode a 0 ∈ A) ↔ a 0 ∈ Values.gammaPullback A
    rw [GammaSyntax.mem_gammaPullback_iff]
    change ((∀ j, NonzeroRV (a j)) ∧ codeValue (a 0) ∈ A) ↔ _
    have hi : (∀ j : Fin 1, NonzeroRV (a j)) ↔ NonzeroRV (a 0) := by
      exact ⟨fun h => h 0,fun h j => by fin_cases j; exact h⟩
    rw [hi]
  change FullBaseAtomicity.OverBase B _ ↔ FullBaseAtomicity.OverBase B _
  rw [he]

theorem unary_at {A : Set (Values.Gamma (M := M))} (hA : Scalar B A) (i : ι) :
    Definable B (fun a : ι → Values.Gamma (M := M) => a i ∈ A) :=
  ((scalar_definable_iff A).mpr hA).reindex (fun _ : Fin 1 => i)

theorem one_definable (B : FullBaseAtomicity.Base (M := M)) :
    Scalar B {(1 : Values.Gamma (M := M))} :=
  Scalar.of_real (GammaSyntax.one_definable B.real)

end IntegrationInACVF.Section3ACVF.FullGammaSyntax
