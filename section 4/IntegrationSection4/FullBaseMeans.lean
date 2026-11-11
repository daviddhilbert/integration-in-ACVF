import IntegrationSection4.FullBaseFunctions
import IntegrationSection3ACVF.FullFibreMeans

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FullBaseMeans

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem zero_graph {α : Type} [Finite α] (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseFunctions.Graph B (fun _ : α → M => (0 : VFType (M := M)).val) := by
  let z0 := @iVFZero M sM
  have hz : @iVFZero M (@CanonicalStructure.normalize M sM) = z0 :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  apply FullBaseAtomicity.OverBase.of_real
  letI := @CanonicalStructure.normalize M sM
  have hc : B.real.DefinableFun LRV (fun _ : α ⊕ Fin 1 → M => z0) := by
    rw [← hz]
    exact SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  exact (Set.DefinableFun.proj LRV).ofPred_eq hc

/-- The mean graph of every bounded finite VF family, including its empty
rows, is definable over the unchanged interpreted base. -/
theorem mean_graph (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B
      {z : Fin n ⊕ Fin 1 → M | ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)})
    (N : ℕ) (hN : ∀ t, (F t).card ≤ N) :
    FullBaseFunctions.Graph B (fun t => (Barycentre.mean (F t)).val) := by
  let T : Set (Fin n → M) := {t | (F t).Nonempty}
  have hT : FullBaseAtomicity.OverBase B T := by
    have h := FullBaseAtomicity.OverBase.exists_block hF
    apply FullBaseAtomicity.OverBase.congr h
    intro t
    change (∃ x : Fin 1 → M, ∃ y ∈ F t, y.val = x 0) ↔ (F t).Nonempty
    exact ⟨fun ⟨_,y,hy,_⟩ => ⟨y,hy⟩,fun ⟨y,hy⟩ => ⟨![y.val],y,hy,rfl⟩⟩
  have hMean := FullFibreMeans.bounded_graph_definable B h00 F hF T hT (fun _ h => h) N (fun t _ => hN t)
  have hEmpty := FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hT.compl (Sum.inl : Fin n → Fin n ⊕ Fin 1)) (zero_graph B)
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.union hMean hEmpty)
  intro z
  change ((F (z ∘ Sum.inl)).Nonempty ∧ z (.inr 0) = (Barycentre.mean (F (z ∘ Sum.inl))).val) ∨
    (¬ (F (z ∘ Sum.inl)).Nonempty ∧ z (.inr 0) = (0 : VFType (M := M)).val) ↔
      z (.inr 0) = (Barycentre.mean (F (z ∘ Sum.inl))).val
  by_cases hn : (F (z ∘ Sum.inl)).Nonempty
  · simp only [hn,true_and,not_true_eq_false,false_and,or_false]
  · have he : F (z ∘ Sum.inl) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he,Barycentre.mean]

end IntegrationInACVF.Section4.FullBaseMeans
