import IntegrationSection3ACVF.FullBaseLogic

/-! Graph composition for functions definable over the full interpreted
parameter base. All intermediate values are quantified, not named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FullBaseFunctions

variable {M α β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable [Finite α] [Finite β]

def Graph (B : FullBaseAtomicity.Base (M := M)) (f : (α → M) → M) : Prop :=
  FullBaseAtomicity.OverBase B {z : α ⊕ Fin 1 → M | z (.inr 0) = f (z ∘ Sum.inl)}

theorem projection (B : FullBaseAtomicity.Base (M := M)) (i : α) : Graph B (fun z : α → M => z i) := by
  apply FullBaseAtomicity.OverBase.of_real
  letI := @CanonicalStructure.normalize M sM
  exact SpecialTransformations.Section3.RawClosure.definable_equal_coordinates B.real (Sum.inr 0 : α ⊕ Fin 1) (Sum.inl i)

theorem comp (B : FullBaseAtomicity.Base (M := M)) {f : (α → M) → M}
    (hf : Graph B f) {g : (β → M) → (α → M)}
    (hg : ∀ i, Graph B (fun z => g z i)) : Graph B (fun z => f (g z)) := by
  let ι := (β ⊕ Fin 1) ⊕ α
  have hCoords (i : α) : FullBaseAtomicity.OverBase B
      {z : ι → M | z (.inr i) = g ((z ∘ Sum.inl) ∘ Sum.inl) i} :=
    FullBaseAtomicity.OverBase.preimage_comp (hg i)
      (Sum.elim (fun j => .inl (.inl j)) (fun _ => .inr i) : β ⊕ Fin 1 → ι)
  have hF := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim Sum.inr (fun _ : Fin 1 => (.inl (.inr 0) : ι)))
  have hAll := FullBaseAtomicity.OverBase.forall_finite hCoords
  have h := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hAll hF)
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∃ a : α → M, (∀ i, a i = g (z ∘ Sum.inl) i) ∧ z (.inr 0) = f a) ↔
    z (.inr 0) = f (g (z ∘ Sum.inl))
  exact ⟨fun ⟨a,ha,hf⟩ => funext ha ▸ hf,fun h => ⟨g (z ∘ Sum.inl),fun _ => rfl,h⟩⟩

theorem tuple_graph (B : FullBaseAtomicity.Base (M := M)) {ι : Type} [Finite ι]
    {f : (α → M) → (ι → M)} (hf : ∀ i, Graph B (fun z => f z i)) :
    FullBaseAtomicity.OverBase B {z : α ⊕ ι → M | z ∘ Sum.inr = f (z ∘ Sum.inl)} := by
  have h := FullBaseAtomicity.OverBase.forall_finite (fun i =>
    FullBaseAtomicity.OverBase.preimage_comp (hf i) (Sum.elim Sum.inl (fun _ : Fin 1 => .inr i) : α ⊕ Fin 1 → α ⊕ ι))
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

end IntegrationInACVF.Section4.FullBaseFunctions
