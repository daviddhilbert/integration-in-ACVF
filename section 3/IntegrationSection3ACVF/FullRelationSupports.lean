import IntegrationSection3ACVF.CanonicalRegions
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3.FibreSupportFormulas
import IntegrationSection3.RelationalPreimages
import IntegrationSection3.ProperInverseSupports

/-! ACVF bridge for the inverse-image support invariants in 3.11.
The joint support graph retains every real code of both ball names. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.FullRelationSupports

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

def preimages (R : Set (M × M)) : BallImaginaries.Ball M → Set M :=
  RelationalPreimages.family R (BallImaginaries.underlying (M := M))

theorem preimages_definable (B : FullBaseAtomicity.Base (M := M))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    FullBaseAtomicity.Relation B (preimages (M := M) R) := by
  let C := preimages (M := M) R
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact RelationalPreimages.family_definable hp hR
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm)

theorem support_graph_definable (B : FullBaseAtomicity.Base (M := M))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R}) (n : ℕ) :
    FullBaseAtomicity.OverBase B
      ((ImaginaryParameters.tuplePresentation (@BallPresentation.presentation M sM hM) (Fin 2)).pullback
        {a | FibreSupportFormulas.SupportMember (BallImaginaries.underlying (M := M))
          (preimages R) n (a 0) (a 1)}) := by
  let C := preimages (M := M) R
  have hPre := preimages_definable B hR
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.presentation_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact FibreSupportFormulas.supportMember_definable hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hPre n

theorem uniform_support_card (B : FullBaseAtomicity.Base (M := M))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    {A : Set M} (hAtomic : FullBallCoset.CompleteType B A)
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T)
    (hsub : ∀ j ∈ T, BallImaginaries.underlying j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (BallImaginaries.underlying j) (BallImaginaries.underlying k))
    {j k : BallImaginaries.Ball M} (hj : j ∈ T) (hk : k ∈ T) {F G : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (preimages R j))
    (hG : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) G (preimages R k)) :
    F.card = G.card := by
  let C := preimages (M := M) R
  let balls := {b : Set M | IsBall b}
  have hFb : MinimalBallSupport.IsMinimalSupport balls F (C j) :=
    ⟨⟨minimal_support_encoded hF,hF.1.2⟩,fun H hH =>
      hF.2 H ⟨fun b hb => Or.inl (hH.1 b hb),hH.2⟩⟩
  have hGb : MinimalBallSupport.IsMinimalSupport balls G (C k) :=
    ⟨⟨minimal_support_encoded hG,hG.1.2⟩,fun H hH =>
      hG.2 H ⟨fun b hb => Or.inl (hH.1 b hb),hH.2⟩⟩
  have hPre := preimages_definable B hR
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hne (i : BallImaginaries.Ball M) (_ : i ∈ T) : (U i).Nonempty :=
    encodedBall_nonempty (BallCodeGeometry.underlying_isBall i)
  have hUballs (i : BallImaginaries.Ball M) : U i ∈ balls := BallCodeGeometry.underlying_isBall i
  have hcodes : ∀ b ∈ balls, ∃ i, U i = b := BallCodeGeometry.encodedBall_coded
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact FibreSupportFormulas.uniform_minimal_card hp hq
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) hPre
    hUballs hcodes
    hAtomic hT (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm)
    hne hsub hdis hj hk hFb hGb

/-- First geometric step of corrected 3.11: every canonical inverse
support ball is proper in the source atomic ball. The finite fibre bound
comes from atomicity and counting, with no saturation or smallness premise. -/
theorem exists_proper_inverse_supports (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (i : BallImaginaries.Ball M) (hi : AdjoinBall.AtomicOver B (BallImaginaries.underlying i))
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hsource : ∀ x y, (x,y) ∈ R → x ∈ BallImaginaries.underlying i)
    (hfinite : ∀ x ∈ BallImaginaries.underlying i, {y | (x,y) ∈ R}.Finite)
    {A : Set M} (hAtomic : FullBallCoset.CompleteType B A)
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T) (hTinfinite : T.Infinite)
    (hsub : ∀ j ∈ T, BallImaginaries.underlying j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (BallImaginaries.underlying j) (BallImaginaries.underlying k)) :
    ∃ F : BallImaginaries.Ball M → Finset (Set M),
      (∀ j ∈ T, MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) (F j) (preimages R j)) ∧
        ∀ j ∈ T, ∀ b ∈ F j, b ⊂ BallImaginaries.underlying i := by
  classical
  let C := preimages (M := M) R
  have hSource (j : BallImaginaries.Ball M) (_ : j ∈ T) : C j ⊆ U i := by
    rintro x ⟨y,hr,_⟩
    exact hsource x y hr
  have hPre := preimages_definable B hR
  have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
  have hsupp (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      HasFiniteBallSupport {b : Set M | IsBall b} (C j) := by
    have hCvf := (hSource j hj).trans (BallImaginaries.underlying_subset_vf i)
    let p := @ParameterPresentation.presentation M sM hM
    let q := @BallPresentation.presentation M sM hM
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.finite_ball_support hcm hPre j hCvf
  have heach (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      ∃ F, MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (C j) :=
    MinimalBallSupport.exists_minimal_support ((hsupp j hj).mono (fun b hb => Or.inl hb))
  let F : BallImaginaries.Ball M → Finset (Set M) :=
    fun j => if hj : j ∈ T then Classical.choose (heach j hj) else ∅
  have hF (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) (F j) (C j) := by
    dsimp only [F]
    rw [dite_eq_left hj]
    exact Classical.choose_spec (heach j hj)
  have hcodes (j : BallImaginaries.Ball M) (hj : j ∈ T) : ∀ b ∈ F j, ∃ k, U k = b :=
    fun b hb => BallCodeGeometry.encodedBall_coded b (minimal_support_encoded (hF j hj) b hb)
  have hne (j : BallImaginaries.Ball M) (_ : j ∈ T) : (U j).Nonempty :=
    encodedBall_nonempty (BallCodeGeometry.underlying_isBall j)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.presentation_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hinj := BallImaginaries.underlying_injective (M := M)
  have hballs (j : BallImaginaries.Ball M) : U j ∈ ballFamily (M := M) :=
    Or.inl (BallCodeGeometry.underlying_isBall j)
  have hlam := ballFamily_laminar (M := M)
  have hnf := ballFamily_avoids δ hδ
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  refine ⟨F,hF,?_⟩
  letI := CanonicalStructure.normalize (M := M)
  have hU := ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm
  exact ProperInverseSupports.proper_inverse_supports hp hq hU hinj hU hR hlam
    (Or.inr rfl) hnf hballs i hi.1 hi.2 hfinite hAtomic hT hTinfinite hne hsub hdis
    F hF hcodes hSource

end IntegrationInACVF.Section3ACVF.FullRelationSupports
