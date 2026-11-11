import IntegrationSection3ACVF.FullBaseDefinability
import Section3.GammaCounting

/-! Finite distinct witnesses for actual full-base unary relation rows.
The counting predicate keeps every context label free and every original
imaginary parameter, without specializing its codes. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullBaseCounting

variable {M α : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def row (R : Set (α ⊕ Fin 1 → M)) (a : α → M) : Set M := {x | Sum.elim a ![x] ∈ R}
def hasMore (R : Set (α ⊕ Fin 1 → M)) (k : ℕ) : Set (α → M) :=
  {a | ∃ x : Fin (k+1) → M, Function.Injective x ∧ ∀ i, x i ∈ row R a}

theorem hasMore_definable [Finite α] (B : FullBaseAtomicity.Base (M := M))
    (R : Set (α ⊕ Fin 1 → M)) (hR : FullBaseAtomicity.OverBase B R) (k : ℕ) :
    FullBaseAtomicity.OverBase B (hasMore R k) := by
  let ι := α ⊕ Fin (k+1)
  have hMem (i : Fin (k+1)) : FullBaseAtomicity.OverBase B
      {z : ι → M | Sum.elim (z ∘ Sum.inl) ![z (.inr i)] ∈ R} := by
    have hd := FullBaseAtomicity.OverBase.preimage_comp hR (Sum.map id (fun _ : Fin 1 => i))
    apply FullBaseAtomicity.OverBase.congr hd
    intro z
    have he : z ∘ Sum.map id (fun _ : Fin 1 => i) = Sum.elim (z ∘ Sum.inl) ![z (.inr i)] := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j; rfl
    change (z ∘ Sum.map id (fun _ : Fin 1 => i) ∈ R) ↔ _
    rw [he]
    rfl
  have hNe (p : Fin (k+1) × Fin (k+1)) : FullBaseAtomicity.OverBase B
      {z : ι → M | p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)} := by
    by_cases he : p.1 = p.2
    · have hu : FullBaseAtomicity.OverBase B (Set.univ : Set (ι → M)) := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact Set.definable_univ
      apply FullBaseAtomicity.OverBase.congr hu
      intro z
      simp only [Set.mem_univ,Set.mem_ofPred_eq,he,true_or]
    · have hEq : FullBaseAtomicity.OverBase B {z : ι → M | z (.inr p.1) = z (.inr p.2)} := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact RawClosure.definable_equal_coordinates B.real (Sum.inr p.1 : ι) (Sum.inr p.2 : ι)
      apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.compl hEq)
      intro z
      change (z (.inr p.1) ≠ z (.inr p.2)) ↔ _
      exact ⟨Or.inr,fun h => h.resolve_left he⟩
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.forall_finite hNe) (FullBaseAtomicity.OverBase.forall_finite hMem))
  apply FullBaseAtomicity.OverBase.congr hd
  intro a
  change (∃ x : Fin (k+1) → M, (∀ p : Fin (k+1) × Fin (k+1), p.1 = p.2 ∨ x p.1 ≠ x p.2) ∧
    ∀ i, Sum.elim a ![x i] ∈ R) ↔ _
  constructor
  · rintro ⟨x,hNe,hMem⟩
    refine ⟨x,?_,hMem⟩
    intro i j he
    exact (hNe (i,j)).resolve_right (fun hn => hn he)
  · rintro ⟨x,hInj,hMem⟩
    refine ⟨x,?_,hMem⟩
    intro p
    by_cases he : p.1 = p.2
    · exact Or.inl he
    · exact Or.inr (fun h => he (hInj h))

theorem hasMore_iff (R : Set (α ⊕ Fin 1 → M)) (a : α → M) (k : ℕ) :
    a ∈ hasMore R k ↔ ¬ ((row R a).Finite ∧ (row R a).ncard ≤ k) := by
  have h := GammaParameters.no_injection_iff_finite_ncard_le (A := row R a) (d := k)
  constructor
  · intro hx hFinite
    exact h.mpr hFinite hx
  · intro hn
    by_contra hNo
    exact hn (h.mp hNo)

end IntegrationInACVF.Section3ACVF.FullBaseCounting
