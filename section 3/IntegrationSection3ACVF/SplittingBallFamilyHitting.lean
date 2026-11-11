import IntegrationSection3ACVF.RealBallFamilyAvoidance
import IntegrationSection3ACVF.RealBallAtomicity
import IntegrationSection3ACVF.CanonicalBallSupport
import IntegrationSection3.FiniteSupportHitting
import Section3.SmallFiniteParameters

/-! A full original-base definable family of split balls has an
arbitrary finite real hitting set. Imaginary codes are specialized only
inside this existence proof; the hitting points need not be named. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.SplittingBallFamilyHitting

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_hitting_set {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    (T : Set (BallImaginaries.Ball M)) (hT : FullBaseAtomicity.Family B T)
    (P : BallImaginaries.Ball M → Set M) (hP : FullBaseAtomicity.Relation B P)
    (hBad : ∀ i ∈ T, Splits (P i) (BallImaginaries.underlying i)) :
    ∃ F : Finset M, ∀ i ∈ T, ∃ x ∈ F, x ∈ BallImaginaries.underlying i := by
  classical
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hTSpecial : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (@CanonicalStructure.normalize M sM) (Fin 4) (q.pullback T) := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryParameters.OverBase.specialize (p := p) hT
  have hPSpecial : ∃ E : Set M, E.Finite ∧
      @Set.Definable M (B.real ∪ E) LRV (@CanonicalStructure.normalize M sM) (Fin 4 ⊕ Fin 1)
        (q.relationPullback P) := by
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryParameters.OverBase.specialize (p := p) hP
  obtain ⟨E,hE,hTE⟩ := hTSpecial
  obtain ⟨F,hF,hPF⟩ := hPSpecial
  let S := B.real ∪ (E ∪ F)
  let C : FullBaseAtomicity.Base (M := M) := ⟨S,∅⟩
  have hSmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall (E ∪ F) (hE.union hF)
  have hTEsub : B.real ∪ E ⊆ S := fun x hx => by
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
  have hPFsub : B.real ∪ F ⊆ S := fun x hx => by
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have hTC : FullBaseAtomicity.Family C T := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact hTE.mono hTEsub
  have hPC : FullBaseAtomicity.Relation C P := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact hPF.mono hPFsub
  have hOnly : ∀ i ∈ C.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ := by
    intro i hi
    exact (Set.notMem_empty i hi).elim
  have hAtomic {A : Set M} (hA : FullBallCoset.CompleteType C A)
      (i : BallImaginaries.Ball M) (_hi : i ∈ T) (hsub : BallImaginaries.underlying i ⊆ A) :
      AdjoinBall.AtomicOver (C.adjoin (Sum.inl i)) (BallImaginaries.underlying i) :=
    RealBallAtomicity.atomic_gamma_base h00 δ hδ1 C hOnly hA i hsub
  obtain ⟨G,hG,hCover⟩ := RealBallFamilyAvoidance.finite_cover hs C rfl hSmallS T hTC P hPC hBad hAtomic
  have hSupport (U : Set M) (hU : U ∈ G) : HasFiniteBallSupport {D : Set M | IsBall D} U := by
    have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
    letI := @CanonicalStructure.normalize M sM
    exact ImaginaryParameters.finite_ball_support hcm (hG U hU).2.1 (hG U hU).1
  apply FiniteSupportHitting.finite_hitting_set {D : Set M | IsBall D} encodedBalls_laminar
    (fun D hD => CanonicalBallSupport.encodedBall_nonempty hD) T BallImaginaries.underlying
    (fun i _ => BallCodeGeometry.underlying_isBall i) G hSupport
  · intro i hi x hx
    exact hCover x (BallImaginaries.underlying_subset_vf i hx)
  · intro i hi U hU
    exact (hG U hU).2.2 i hi

end IntegrationInACVF.Section3ACVF.SplittingBallFamilyHitting
