import IntegrationSection4.FiniteScalarFamilies
import IntegrationSection4.LocalConstancyFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyLocalConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

/-- The locally constant locus is definable with all family parameters free. -/
theorem locus_definable (B : FullBaseAtomicity.Base (M := M)) {n : ℕ}
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      z (.inr 0) ∈ LocalConstancySyntax.locus (A (z ∘ Sum.inl)) (f (z ∘ Sum.inl))} := by
  let ι := ((Fin n ⊕ Fin 4) ⊕ Fin 1) ⊕ Fin 1
  have hm := FullBaseAtomicity.OverBase.preimage_comp (OpenImageConfigurations.body_definable B)
    (Sum.elim (fun i => .inl (.inl (.inr i))) Sum.inr : Fin 4 ⊕ Fin 1 → ι)
  have hg := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl (.inl i))) Sum.inr)
      (fun _ => .inl (.inr 0)) : (Fin n ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hConst := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B hm hg))
  have ho := FullBaseAtomicity.OverBase.preimage_comp
    (FullBaseAtomicity.OverBase.of_real (B := B) (BallKindPredicates.chartCodes_definable B.real).1)
    (Sum.inr : Fin 4 → Fin n ⊕ Fin 4)
  have hc := FullBaseAtomicity.OverBase.inter ho hConst
  let j := (Fin n ⊕ Fin 1) ⊕ Fin 4
  have hc' := FullBaseAtomicity.OverBase.preimage_comp hc
    (Sum.elim (fun i => .inl (.inl i)) Sum.inr : Fin n ⊕ Fin 4 → j)
  have hm' := FullBaseAtomicity.OverBase.preimage_comp (OpenImageConfigurations.body_definable B)
    (Sum.elim Sum.inr (fun _ => .inl (.inr 0)) : Fin 4 ⊕ Fin 1 → j)
  exact FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hc' hm')

/-- Every fixed parameter row has finite locally constant image and finite
fibres away from its locally constant locus. Real representatives of the
finitely supported imaginary parameters are used only inside this proof. -/
theorem finite_rows {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {n : ℕ}
    (A : (Fin n → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin n → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph B A f) (p : Fin n → M) :
    (f p '' LocalConstancySyntax.locus (A p) (f p)).Finite ∧
      ∀ y, {x | x ∈ A p \ LocalConstancySyntax.locus (A p) (f p) ∧ f p x = y}.Finite := by
  let C := RealParameterTuples.extend B p
  have hCsmall := RealParameterTuples.small hκ B hsmall p
  have hh := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim Sum.inl (fun _ => .inr 0)) (fun _ => .inr 1) :
      (Fin n ⊕ Fin 1) ⊕ Fin 1 → Fin n ⊕ Fin 2)
  have hRow : FullBaseAtomicity.OverBase C (ImaginaryBaseImages.graphOn (A p) (f p)) := by
    exact RealParameterTuples.specialize B p hh
  have hex : ∃ E : Set M, E.Finite ∧ @Set.Definable M (C.real ∪ E) LRV N (Fin 2)
      (ImaginaryBaseImages.graphOn (A p) (f p)) := by
    letI := N
    exact ImaginaryParameters.OverBase.specialize hRow
  obtain ⟨E,hE,hRaw⟩ := hex
  have hS := small_union_finite hκ C.real hCsmall E hE
  exact ⟨LocalConstancyFibres.finite_image_on_locus hκ hs _ hS h00 δ hδ
      (A p) (hAVF p) (f p) (hfVF p) hRaw,
    LocalConstancyFibres.finite_fibres_off_locus _ (A p) (hAVF p) (f p) hRaw⟩

end IntegrationInACVF.Section4.FamilyLocalConstancy
