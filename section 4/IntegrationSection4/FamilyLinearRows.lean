import IntegrationSection4.FiniteScalarFamilies
import IntegrationSection3ACVF.GammaLinearBallRow

/-! The complete radius/slope relation with free family parameters.
This is the checked GammaLinearBallRow construction with the context
carried through each quantifier, rather than named in the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyLinearRows

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem outputs_definable (B : FullBaseAtomicity.Base (M := M)) {n : ℕ}
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 5 → M |
      GammaLinearBallRow.outputs (A (z ∘ Sum.inl)) (f (z ∘ Sum.inl)) (z ∘ Sum.inr)} := by
  have h0 := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim Sum.inl (fun _ => .inr 1)) (fun _ => .inr 3) :
      (Fin n ⊕ Fin 1) ⊕ Fin 1 → Fin n ⊕ Fin 5)
  have h1 := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim Sum.inl (fun _ => .inr 2)) (fun _ => .inr 4) :
      (Fin n ⊕ Fin 1) ⊕ Fin 1 → Fin n ⊕ Fin 5)
  have hVF := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have h3 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (fun _ : Fin 1 => (Sum.inr 3 : Fin n ⊕ Fin 5))
  have h4 := FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.of_real (B := B) hVF)
    (fun _ : Fin 1 => (Sum.inr 4 : Fin n ⊕ Fin 5))
  have hV := FullBaseAtomicity.OverBase.preimage_comp (GammaLinearValueRow.definable B)
    (Sum.inr : Fin 5 → Fin n ⊕ Fin 5)
  exact FullBaseAtomicity.OverBase.inter h0 (FullBaseAtomicity.OverBase.inter h1
    (FullBaseAtomicity.OverBase.inter h3 (FullBaseAtomicity.OverBase.inter h4 hV)))

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) {n : ℕ}
    (A : (Fin n → M) → Set M) (f : (Fin n → M) → M → M)
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 3 → M |
      GammaLinearBallRow.row (A (z ∘ Sum.inl)) (f (z ∘ Sum.inl)) (z ∘ Sum.inr)} := by
  let ι := (Fin n ⊕ Fin 3) ⊕ Fin 2
  let υ := ι ⊕ Fin 2
  have hOutput := FullBaseAtomicity.OverBase.preimage_comp (outputs_definable B A f hf)
    (Sum.elim (fun i => .inl (.inl (.inl i)))
      (![.inl (.inl (.inr 1)),.inl (.inr 0),.inl (.inr 1),.inr 0,.inr 1] : Fin 5 → υ) : Fin n ⊕ Fin 5 → υ)
  have hExist := FullBaseAtomicity.OverBase.exists_block hOutput
  have hBall0 := FullBaseAtomicity.OverBase.preimage_comp (UniformGammaBallSyntax.ball_definable B)
    (![.inl (.inr 0),.inr 0,.inl (.inr 2)] : Fin 3 → ι)
  have hBall1 := FullBaseAtomicity.OverBase.preimage_comp (UniformGammaBallSyntax.ball_definable B)
    (![.inl (.inr 0),.inr 1,.inl (.inr 2)] : Fin 3 → ι)
  have hPrem := FullBaseAtomicity.OverBase.inter hBall0 hBall1
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.implication B hPrem hExist)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  rfl

end IntegrationInACVF.Section4.FamilyLinearRows
