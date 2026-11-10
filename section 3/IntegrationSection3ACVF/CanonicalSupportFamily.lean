import IntegrationSection3ACVF.CanonicalBallSupport
import IntegrationSection3ACVF.BallCodeGeometry
import IntegrationSection3.SupportFormulas

/-! Original-base definability of the canonical finite ball support.
The formula quantifies every tuple of real codes of the requisite length;
uniqueness identifies its range with the support without naming an enumeration. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.CanonicalSupportFamily

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem support_family_definable (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {F : Finset (Set M)} {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A) :
    FullBaseAtomicity.Family B {i | BallImaginaries.underlying i ∈ F} := by
  let U := BallImaginaries.underlying (M := M)
  have he : SupportFormulas.SupportFamily U A F.card = {i | U i ∈ F} :=
    SupportFormulas.supportFamily_eq_preimage BallImaginaries.underlying_injective
      ballFamily_laminar (Or.inr rfl) (ballFamily_avoids δ hδ) hF
      (fun i => Or.inl (BallCodeGeometry.underlying_isBall i))
      (fun b hb => BallCodeGeometry.encodedBall_coded b (minimal_support_encoded hF b hb))
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.presentation_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hd : FullBaseAtomicity.Family B (SupportFormulas.SupportFamily U A F.card) := by
    letI := CanonicalStructure.normalize (M := M)
    exact SupportFormulas.supportFamily_definable hp hq
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hA F.card
  simpa only [he] using hd

/-- Every original-base definable VF set has an intrinsic finite support
whose entire actual-ball family is definable over that same interpreted base.
This is the canonical-support step, not the primitive-type classification. -/
theorem exists_definable_canonical_support (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (A : Set M)
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) :
    ∃ F : Finset (Set M), MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A ∧
      FullBaseAtomicity.Family B {i | BallImaginaries.underlying i ∈ F} ∧
        {i : BallImaginaries.Ball M | BallImaginaries.underlying i ∈ F}.Finite := by
  obtain ⟨F,hF,_⟩ := exists_unique_minimal_support B δ hδ A hA hAVF
  refine ⟨F,hF,support_family_definable B δ hδ hA hF,?_⟩
  exact F.finite_toSet.preimage BallImaginaries.underlying_injective.injOn

end IntegrationInACVF.Section3ACVF.CanonicalSupportFamily
