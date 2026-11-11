import IntegrationSection3ACVF.GammaFunctionSyntax

/-! Actual images and partial preimages of Gamma sets over the original
interpreted base. No definability of a total graph off its domain. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.GammaFunctionSets

open FullGammaSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem preimage_definable (B : FullBaseAtomicity.Base (M := M))
    (D A : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph D f)) (hA : Scalar B A) :
    Scalar B (D ∩ f ⁻¹' A) := by
  let ι := Fin 1 ⊕ Fin 1
  have hd := ((hG.reindex (![.inl 0,.inr 0] : Fin 2 → ι)).and
    (unary_at hA (Sum.inr 0 : ι))).exists_block
  apply (scalar_definable_iff (D ∩ f ⁻¹' A)).mp
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), (a 0 ∈ D ∧ b 0 = f (a 0)) ∧ b 0 ∈ A) ↔
    (a 0 ∈ D ∧ f (a 0) ∈ A)
  exact ⟨fun ⟨_,⟨hx,he⟩,ha⟩ => ⟨hx,he ▸ ha⟩,fun ⟨hx,ha⟩ => ⟨![f (a 0)],⟨hx,rfl⟩,ha⟩⟩

theorem image_definable (B : FullBaseAtomicity.Base (M := M))
    (D A : Set (Values.Gamma (M := M))) (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph D f)) (hA : Scalar B A) (hAD : A ⊆ D) :
    Scalar B (f '' A) := by
  let ι := Fin 1 ⊕ Fin 1
  have hd := ((hG.reindex (![.inr 0,.inl 0] : Fin 2 → ι)).and
    (unary_at hA (Sum.inr 0 : ι))).exists_block
  apply (scalar_definable_iff (f '' A)).mp
  apply hd.congr
  intro a
  change (∃ b : Fin 1 → Values.Gamma (M := M), (b 0 ∈ D ∧ a 0 = f (b 0)) ∧ b 0 ∈ A) ↔ a 0 ∈ f '' A
  exact ⟨fun ⟨b,⟨_,he⟩,hb⟩ => ⟨b 0,hb,he.symm⟩,fun ⟨x,hx,he⟩ => ⟨![x],⟨hAD hx,he.symm⟩,hx⟩⟩

end IntegrationInACVF.Section3ACVF.GammaFunctionSets
