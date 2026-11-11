import IntegrationSection3ACVF.FullGammaSyntax
import Section3.GammaCounting

/-! Distinct witnesses on the actual Gamma quotient, retaining the full
original interpreted parameter base and all proper code representatives. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.FullGammaCounting

variable {M α : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def row (P : (α ⊕ Fin 1 → Values.Gamma (M := M)) → Prop)
    (a : α → Values.Gamma (M := M)) : Set (Values.Gamma (M := M)) :=
  {x | P (Sum.elim a ![x])}

def hasMore (P : (α ⊕ Fin 1 → Values.Gamma (M := M)) → Prop) (k : ℕ)
    (a : α → Values.Gamma (M := M)) : Prop :=
  ∃ x : Fin (k+1) → Values.Gamma (M := M), Function.Injective x ∧ ∀ i, x i ∈ row P a

theorem hasMore_definable [Finite α] (B : FullBaseAtomicity.Base (M := M))
    (P : (α ⊕ Fin 1 → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable B P) (k : ℕ) :
    FullGammaSyntax.Definable B (hasMore P k) := by
  let ι := α ⊕ Fin (k+1)
  have hMem (i : Fin (k+1)) : FullGammaSyntax.Definable B
      (fun z : ι → Values.Gamma (M := M) => P (Sum.elim (z ∘ Sum.inl) ![z (.inr i)])) := by
    apply (hP.reindex (Sum.map id (fun _ : Fin 1 => i))).congr
    intro z
    have he : z ∘ Sum.map id (fun _ : Fin 1 => i) = Sum.elim (z ∘ Sum.inl) ![z (.inr i)] := by
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j; rfl
    rw [he]
  have hNe (p : Fin (k+1) × Fin (k+1)) : FullGammaSyntax.Definable B
      (fun z : ι → Values.Gamma (M := M) => p.1 = p.2 ∨ z (.inr p.1) ≠ z (.inr p.2)) := by
    by_cases he : p.1 = p.2
    · apply (FullGammaSyntax.Definable.true_ (ι := ι) B).congr
      intro z
      exact iff_of_true trivial (Or.inl he)
    · apply (FullGammaSyntax.eq_definable B (Sum.inr p.1 : ι) (Sum.inr p.2)).not.congr
      intro z
      exact ⟨Or.inr,fun h => h.resolve_left he⟩
  have hd := ((FullGammaSyntax.Definable.forall_finite hNe).and
    (FullGammaSyntax.Definable.forall_finite hMem)).exists_block
  apply hd.congr
  intro a
  change (∃ x : Fin (k+1) → Values.Gamma (M := M),
    (∀ p : Fin (k+1) × Fin (k+1), p.1 = p.2 ∨ x p.1 ≠ x p.2) ∧
    ∀ i, P (Sum.elim a ![x i])) ↔ _
  constructor
  · rintro ⟨x,hNe,hMem⟩
    exact ⟨x,fun i j he => (hNe (i,j)).resolve_right (fun hn => hn he),hMem⟩
  · rintro ⟨x,hInj,hMem⟩
    refine ⟨x,?_,hMem⟩
    intro p
    by_cases he : p.1 = p.2
    · exact Or.inl he
    · exact Or.inr (fun h => he (hInj h))

theorem hasMore_iff (P : (α ⊕ Fin 1 → Values.Gamma (M := M)) → Prop)
    (a : α → Values.Gamma (M := M)) (k : ℕ) :
    hasMore P k a ↔ ¬ ((row P a).Finite ∧ (row P a).ncard ≤ k) := by
  have h := GammaParameters.no_injection_iff_finite_ncard_le (A := row P a) (d := k)
  exact ⟨fun hx hFin => h.mpr hFin hx,fun hn => by
    by_contra hNo
    exact hn (h.mp hNo)⟩

end IntegrationInACVF.Section3ACVF.FullGammaCounting
