import IntegrationSection3ACVF.ClosedCompleteTypeAtomicity
import IntegrationSection3ACVF.OpenCompleteTypeAtomicity

/-! Actual open/closed classification and real/Gamma atomicity for every
released ball imaginary,including singleton and whole-field cases. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RealBallAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_or_closed (i : BallImaginaries.Ball M) :
    PaperBalls.IsOpenBall (BallImaginaries.underlying i) ∨
      PaperBalls.IsClosedBall (BallImaginaries.underlying i) := by
  obtain ⟨c,hci⟩ := BallPresentation.decode_surjective i
  have he := BallPresentation.underlying_decode c
  rw [hci] at he
  by_cases hflag : c.val 3 = iVFZero
  · have hvalid : ∀ j, iVF (BallPresentation.closedTuple c.val j) :=
      (c.property.resolve_right (fun h => h.1 hflag)).2
    have hClosed := BallKindGeometry.closed_raw_isClosedBall
      (⟨BallPresentation.closedTuple c.val,hvalid⟩ : ClosedBallCodes.Code M)
    rw [if_pos hflag] at he
    exact Or.inr (he.symm ▸ hClosed)
  · have hvalid : OpenBallCodes.Proper (BallPresentation.openTuple c.val) :=
      (c.property.resolve_left (fun h => hflag h.1)).2
    have hOpen := BallKindGeometry.open_raw_isOpenBall
      (⟨BallPresentation.openTuple c.val,hvalid⟩ : OpenBallCodes.Code M)
    rw [if_neg hflag] at he
    exact Or.inl (he.symm ▸ hOpen)

theorem atomic_gamma_base (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  rcases open_or_closed i with ho | hc
  · rcases ho with hWhole | ⟨a,α,hi⟩
    · exact FullGammaRadius.lemma_3_4_whole_field B hA i hWhole hsub
    · exact OpenCompleteTypeAtomicity.lemma_3_4_open_gamma_base h00 δ hδ1 B hOnly hA i a α hi hsub
  · exact ClosedCompleteTypeAtomicity.closed_gamma_base h00 δ hδ1 B hOnly hA i hc hsub

end IntegrationInACVF.Section3ACVF.RealBallAtomicity
