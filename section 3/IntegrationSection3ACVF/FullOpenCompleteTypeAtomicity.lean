import IntegrationSection3ACVF.SplittingBallHitting
import IntegrationSection3ACVF.FiniteHittingAtomicity

/-! The open-ball part of3.4 at arbitrary radii over the full original
real/Gamma/ball base. Neither the ambient complete type nor the ball
radius is required to be definable over that base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullOpenCompleteTypeAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem atomicWith_open {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (ho : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hsub : BallImaginaries.underlying i ⊆ A) :
    FullBaseAtomicity.AtomicWith B i (BallImaginaries.underlying i) := by
  have hm : FullBaseAtomicity.Relation B BallImaginaries.underlying :=
    FullBaseAtomicity.OverBase.of_real (BallPresentation.membership_definable B.real)
  refine ⟨⟨BallImaginaries.underlying,hm,rfl⟩,?_⟩
  rintro U ⟨P,hP,hPi⟩
  have hNoSplit : ¬ Splits U (BallImaginaries.underlying i) := by
    intro hSplit
    let T : Set (BallImaginaries.Ball M) :=
      {j | PaperBalls.IsOpenBall (BallImaginaries.underlying j) ∧
        Splits (P j) (BallImaginaries.underlying j)}
    have hT : FullBaseAtomicity.Family B T := by
      let p := @ParameterPresentation.presentation M sM hM
      let q := @BallPresentation.presentation M sM hM
      have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
      have hq := BallPresentation.codeDomain_definable (M := M) B.real
      have hOpen := BallKindPredicates.open_family_definable B
      letI := @CanonicalStructure.normalize M sM
      exact ImaginaryBaseFamilies.exceptional_definable (p := p) (q := q) hp hq hOpen hm hP
    have hi : i ∈ T := ⟨ho,hPi.symm ▸ hSplit⟩
    obtain ⟨F,hHit⟩ := SplittingBallHitting.finite_hitting_set hκ hs B hsmall h00 δ hδ1 T hT P hP
      (fun j hj => hj)
    have hAtomic := FiniteHittingAtomicity.atomicWith B δ hδ1 T hT F hHit hA i hi hsub
    obtain ⟨x,hx,hxU,y,hy,hyU⟩ := hSplit
    rcases hAtomic.2 U ⟨P,hP,hPi⟩ with hAll | hDis
    · exact hyU (hAll hy)
    · exact Set.disjoint_left.mp hDis hx hxU
  by_cases hAll : BallImaginaries.underlying i ⊆ U
  · exact Or.inl hAll
  · obtain ⟨y,hy,hyU⟩ := Set.not_subset.mp hAll
    exact Or.inr (Set.disjoint_left.mpr fun x hx hxU => hNoSplit ⟨x,hx,hxU,y,hy,hyU⟩)

theorem lemma_3_4_open {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ1 : 1 < δ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (ho : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) :=
  FullBallCoset.atomicWith_to_adjoin B i _ (atomicWith_open hκ hs B hsmall h00 δ hδ1 hA i ho hsub)

end IntegrationInACVF.Section3ACVF.FullOpenCompleteTypeAtomicity
