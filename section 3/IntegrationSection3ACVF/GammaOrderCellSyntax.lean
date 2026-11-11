import IntegrationSection3ACVF.FiniteOrderCells
import IntegrationSection3ACVF.GammaTupleParameters

/-! Every finite-order code cell is definable after adjoining exactly
its finitely many actual Gamma endpoints. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaOrderCellSyntax

open FullGammaSyntax FiniteOrderCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem sign_definable {α : Type} [Finite α] (B : FullBaseAtomicity.Base (M := M))
    (i j : α) (b : Bool) : Definable B (fun a : α → Values.Gamma (M := M) => decide (a i < a j) = b) := by
  cases b
  · apply (lt_definable B i j).not.congr
    intro a
    exact ⟨decide_eq_false,of_decide_eq_false⟩
  · apply (lt_definable B i j).congr
    intro a
    exact ⟨decide_eq_true,of_decide_eq_true⟩

theorem cell_definable (B : FullBaseAtomicity.Base (M := M))
    (F : Finset (Values.Gamma (M := M))) (c : Code F) :
    Scalar (GammaTupleParameters.extend B (fun t : F => t.val)) (cell F c) := by
  let ι := F ⊕ Fin 1
  have hEach (t : F) : Definable B (fun a : ι → Values.Gamma (M := M) =>
      a (.inr 0) ≠ a (.inl t) ∧
      decide (a (.inr 0) < a (.inl t)) = (c t).1 ∧
      decide (a (.inl t) < a (.inr 0)) = (c t).2) :=
    ((eq_definable B (Sum.inr 0 : ι) (Sum.inl t)).not).and
      ((sign_definable B (Sum.inr 0 : ι) (Sum.inl t) (c t).1).and
        (sign_definable B (Sum.inl t : ι) (Sum.inr 0) (c t).2))
  have hd := GammaTupleParameters.specialize B (fun t : F => t.val) (Definable.forall_finite hEach)
  apply (scalar_definable_iff (cell F c)).mp
  apply hd.congr
  intro a
  change (∀ t : F, a 0 ≠ t.val ∧ decide (a 0 < t.val) = (c t).1 ∧ decide (t.val < a 0) = (c t).2) ↔
    (a 0 ∉ F ∧ code F (a 0) = c)
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro haF
      exact (h ⟨a 0,haF⟩).1 rfl
    · funext t
      exact Prod.ext (h t).2.1 (h t).2.2
  · rintro ⟨ha,he⟩ t
    have ht := congrFun he t
    exact ⟨fun h => ha (h.symm ▸ t.property),congrArg Prod.fst ht,congrArg Prod.snd ht⟩

end IntegrationInACVF.Section3ACVF.GammaOrderCellSyntax
