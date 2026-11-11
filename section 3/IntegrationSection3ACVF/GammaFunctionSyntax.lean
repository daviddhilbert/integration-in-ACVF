import IntegrationSection3ACVF.FullGammaControllers

/-! Full original-base syntax for partial actual Gamma functions and
their order comparisons. All formulas keep every proper representative. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaFunctionSyntax

open FullGammaSyntax

variable {M α : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [Finite α]

def graph (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (a : Fin 2 → Values.Gamma (M := M)) : Prop := a 0 ∈ D ∧ a 1 = f (a 0)

theorem domain_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (graph D f)) : Scalar B D := by
  have hd := (hG.reindex (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)).exists_block
  apply (scalar_definable_iff D).mp
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), a 0 ∈ D ∧ b 0 = f (a 0)) ↔ a 0 ∈ D
  exact ⟨fun ⟨_,h,_⟩ => h,fun h => ⟨![f (a 0)],h,rfl⟩⟩

theorem comparison_definable (B : FullBaseAtomicity.Base (M := M))
    (D : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (graph D f)) (i j : α) :
    Definable B (fun a : α → Values.Gamma (M := M) =>
      a i ∈ D ∧ a j ∈ D ∧ f (a i) < f (a j)) := by
  let ι := α ⊕ Fin 2
  have hgI := hG.reindex (![.inl i,.inr 0] : Fin 2 → ι)
  have hgJ := hG.reindex (![.inl j,.inr 1] : Fin 2 → ι)
  have hd := ((hgI.and hgJ).and (lt_definable B (Sum.inr 0 : ι) (Sum.inr 1))).exists_block
  apply hd.congr
  intro a
  change (∃ b : Fin 2 → Values.Gamma (M := M),
    ((a i ∈ D ∧ b 0 = f (a i)) ∧ (a j ∈ D ∧ b 1 = f (a j))) ∧ b 0 < b 1) ↔ _
  constructor
  · rintro ⟨b,⟨⟨hi,h0⟩,hj,h1⟩,hLt⟩
    rw [h0,h1] at hLt
    exact ⟨hi,hj,hLt⟩
  · rintro ⟨hi,hj,hLt⟩
    exact ⟨![f (a i),f (a j)],⟨⟨hi,rfl⟩,hj,rfl⟩,hLt⟩

theorem one_lt_definable (B : FullBaseAtomicity.Base (M := M)) (i : α) :
    Definable B (fun a : α → Values.Gamma (M := M) => 1 < a i) := by
  let ι := α ⊕ Fin 1
  have hd := ((unary_at (one_definable B) (Sum.inr 0 : ι)).and
    (lt_definable B (Sum.inr 0 : ι) (Sum.inl i))).exists_block
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), b 0 = 1 ∧ b 0 < a i) ↔ _
  exact ⟨fun ⟨_,he,h⟩ => he ▸ h,fun h => ⟨![1],rfl,h⟩⟩

theorem mul_lt_definable (B : FullBaseAtomicity.Base (M := M)) (i j k : α) :
    Definable B (fun a : α → Values.Gamma (M := M) => a i * a j < a k) := by
  let ι := α ⊕ Fin 1
  have hd := ((mul_definable B (Sum.inl i : ι) (Sum.inl j) (Sum.inr 0)).and
    (lt_definable B (Sum.inr 0 : ι) (Sum.inl k))).exists_block
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), a i * a j = b 0 ∧ b 0 < a k) ↔ _
  exact ⟨fun ⟨_,he,h⟩ => he.symm ▸ h,fun h => ⟨![a i * a j],rfl,h⟩⟩

theorem lt_mul_definable (B : FullBaseAtomicity.Base (M := M)) (i j k : α) :
    Definable B (fun a : α → Values.Gamma (M := M) => a i < a j * a k) := by
  let ι := α ⊕ Fin 1
  have hd := ((mul_definable B (Sum.inl j : ι) (Sum.inl k) (Sum.inr 0)).and
    (lt_definable B (Sum.inl i : ι) (Sum.inr 0))).exists_block
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), a j * a k = b 0 ∧ a i < b 0) ↔ _
  exact ⟨fun ⟨_,he,h⟩ => he.symm ▸ h,fun h => ⟨![a j * a k],rfl,h⟩⟩

end IntegrationInACVF.Section3ACVF.GammaFunctionSyntax
