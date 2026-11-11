import IntegrationSection3ACVF.AdjoinGamma

/-! Specialize actual Gamma tuples by adjoining exactly their quotient
names. The original real base and every old imaginary name are retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaTupleParameters

open FullGammaSyntax

variable {M α β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def extend (B : FullBaseAtomicity.Base (M := M)) (a : α → Values.Gamma (M := M)) :
    FullBaseAtomicity.Base (M := M) := ⟨B.real,B.imaginary ∪ Set.range (fun i => Sum.inr (a i))⟩

theorem mono [Finite β] (B : FullBaseAtomicity.Base (M := M)) (a : α → Values.Gamma (M := M))
    {P : (β → Values.Gamma (M := M)) → Prop} (hP : Definable B P) :
    Definable (extend B a) P :=
  FullBaseAtomicity.OverBase.mono hP Set.Subset.rfl Set.subset_union_left

theorem named (B : FullBaseAtomicity.Base (M := M)) (a : α → Values.Gamma (M := M)) (i : α) :
    Scalar (extend B a) {a i} := AdjoinGamma.named_scalar _ (Or.inr ⟨i,rfl⟩)

theorem specialize [Finite α] [Finite β] (B : FullBaseAtomicity.Base (M := M))
    (a : α → Values.Gamma (M := M))
    {P : (α ⊕ β → Values.Gamma (M := M)) → Prop} (hP : Definable B P) :
    Definable (extend B a) (fun b : β → Values.Gamma (M := M) => P (Sum.elim a b)) := by
  let C := extend B a
  have hEq : Definable C (fun z : β ⊕ α → Values.Gamma (M := M) => ∀ i, z (.inr i) = a i) :=
    Definable.forall_finite (fun i => unary_at (named B a i) (Sum.inr i : β ⊕ α))
  have hd := (((mono B a hP).reindex (Sum.swap : α ⊕ β → β ⊕ α)).and hEq).exists_block
  apply hd.congr
  intro b
  change (∃ c : α → Values.Gamma (M := M), P (Sum.elim b c ∘ Sum.swap) ∧ ∀ i, c i = a i) ↔ P (Sum.elim a b)
  constructor
  · rintro ⟨c,hc,he⟩
    have hca : c = a := funext he
    subst c
    have hSwap : Sum.elim b a ∘ Sum.swap = Sum.elim a b := by funext j; cases j <;> rfl
    rwa [hSwap] at hc
  · intro hb
    refine ⟨a,?_,fun _ => rfl⟩
    have hSwap : Sum.elim b a ∘ Sum.swap = Sum.elim a b := by funext j; cases j <;> rfl
    rwa [hSwap]

end IntegrationInACVF.Section3ACVF.GammaTupleParameters
