import IntegrationSection3ACVF.BallProfileDefinability
import IntegrationSection3ACVF.CanonicalBallSupport
import IntegrationSection3ACVF.BallCodeGeometry
import IntegrationSection3.TerminalBallCover

/-! A ball in a definable family with an arbitrary finite hitting set
is atomic over its own name when it lies in one original-base complete
type. The auxiliary hitting points are not original parameters. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.FiniteBallProfiles

namespace IntegrationInACVF.Section3ACVF.FiniteHittingAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem atomicWith (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (F : Finset M) (hHit : ∀ i ∈ T, ∃ c ∈ F, c ∈ BallImaginaries.underlying i)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (hi : i ∈ T) (hsub : BallImaginaries.underlying i ⊆ A) :
    FullBaseAtomicity.AtomicWith B i (BallImaginaries.underlying i) := by
  have hLam (j : BallImaginaries.Ball M) (_hj : j ∈ T)
      (k : BallImaginaries.Ball M) (_hk : k ∈ T) :
      BallImaginaries.underlying j ⊆ BallImaginaries.underlying k ∨
      BallImaginaries.underlying k ⊆ BallImaginaries.underlying j ∨
      Disjoint (BallImaginaries.underlying j) (BallImaginaries.underlying k) :=
    encodedBalls_laminar _ (BallCodeGeometry.underlying_isBall j)
      _ (BallCodeGeometry.underlying_isBall k)
  obtain ⟨c,_,hci,hc⟩ := exists_terminal_in_ball T BallImaginaries.underlying hLam F hHit i hi
  have hK := BallProfileDefinability.terminal_definable B T hT
  have hTerminal (x : M) (hx : x ∈ BallImaginaries.underlying i) :
      IsTerminal T BallImaginaries.underlying x := by
    rcases hA {x | IsTerminal T BallImaginaries.underlying x} hK with hAll | hDis
    · exact hAll (hsub hx)
    · exact (Set.disjoint_left.mp hDis (hsub hci) hc).elim
  have hAvoid (H : Finset (Set M))
      (hH : ∀ D ∈ H, ∃ k ∈ T, D = BallImaginaries.underlying k ∧ D ⊂ BallImaginaries.underlying i) :
      ∃ x ∈ BallImaginaries.underlying i, ∀ D ∈ H, x ∉ D := by
    apply CanonicalBallSupport.encoded_avoids_finite_proper_subballs δ hδ
      _ (BallCodeGeometry.underlying_isBall i) H
    intro D hD
    obtain ⟨k,_,rfl,hProper⟩ := hH D hD
    exact ⟨BallCodeGeometry.underlying_isBall k,hProper⟩
  obtain ⟨x,hx,hClass⟩ := TerminalBallCover.ball_eq_terminal_class T BallImaginaries.underlying
    hLam F hHit i hi hAvoid hTerminal
  have hiQ : i ∈ BallProfileDefinability.terminalBalls T := ⟨x,hx,hClass⟩
  have hQ := BallProfileDefinability.terminalBalls_definable B T hT
  have hDis := BallProfileDefinability.terminalBalls_disjoint T
  have hm : FullBaseAtomicity.Relation B BallImaginaries.underlying :=
    FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  letI := @CanonicalStructure.normalize M sM
  exact ImaginaryBaseFamilies.atomic_below_complete_type (p := p) (q := q)
    hp hq hQ hm hDis hA hiQ hsub

theorem atomicOver (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (F : Finset M) (hHit : ∀ i ∈ T, ∃ c ∈ F, c ∈ BallImaginaries.underlying i)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (hi : i ∈ T) (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) :=
  FullBallCoset.atomicWith_to_adjoin B i _ (atomicWith B δ hδ T hT F hHit hA i hi hsub)

end IntegrationInACVF.Section3ACVF.FiniteHittingAtomicity
