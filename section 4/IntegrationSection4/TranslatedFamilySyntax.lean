import IntegrationSection4.FiniteScalarFamilies
import IntegrationSection4.InverseDifferenceSyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.TranslatedFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation {m : ℕ} (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (j : Fin m) (p : Fin m → M) : Set (Fin 2 → M) :=
  {z | z 0 ∈ A p ∧ iVF (z 1) ∧ RVDifferencePairs.difference (z 1) (f p (z 0)) = p j}

theorem definable (B : FullBaseAtomicity.Base (M := M)) {m : ℕ}
    (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M) (j : Fin m)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin m ⊕ Fin 2 → M | z ∘ Sum.inr ∈ relation A f j (z ∘ Sum.inl)} := by
  let ι := (Fin m ⊕ Fin 2) ⊕ Fin 1
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inl (.inr 0))) Sum.inr :
      (Fin m ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hDiff := FullBaseAtomicity.OverBase.preimage_comp (RVDifferencePairs.difference_graph_definable B)
    (![.inl (.inr 1),.inr 0,.inl (.inl j)] : Fin 3 → ι)
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hV := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (fun _ : Fin 1 => (Sum.inl (.inr 1) : ι))
  have hh := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hFun
    (FullBaseAtomicity.OverBase.inter hV hDiff))
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change (∃ y : Fin 1 → M,
    (z (.inr 0) ∈ A (z ∘ Sum.inl) ∧ y 0 = f (z ∘ Sum.inl) (z (.inr 0))) ∧
      iVF (z (.inr 1)) ∧ z (.inl j) = RVDifferencePairs.difference (z (.inr 1)) (y 0)) ↔ _
  constructor
  · rintro ⟨y,⟨hx,hy⟩,hv,he⟩
    exact ⟨hx,hv,by rw [hy] at he; exact he.symm⟩
  · rintro ⟨hx,hv,he⟩
    exact ⟨![f (z ∘ Sum.inl) (z (.inr 0))],⟨hx,rfl⟩,hv,he.symm⟩

end IntegrationInACVF.Section4.TranslatedFamilySyntax
