import IntegrationSection3ACVF.MaximalSubballGeometry
import IntegrationSection3.FiniteCofiniteClasses

/-! Definability and finite/cofinite traces for actual maximal open
classes. The proof uses C-minimal finite support over the stated base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.MaximalSubballFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem contained_family_definable (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A}) :
    FullBaseAtomicity.Family B {j | BallImaginaries.underlying j ⊆ A} := by
  let U := BallImaginaries.underlying (M := M)
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have ha := FullBaseAtomicity.OverBase.preimage_comp hA (Sum.inr : Fin 1 → Fin 4 ⊕ Fin 1)
  letI := CanonicalStructure.normalize (M := M)
  have hU := OverBase.of_real (p := p) (B := B) hm
  have hall := OverBase.forall_block (SupportFormulas.imp_definable hp hU ha) hp
  have hv := OverBase.of_real (p := p) (B := B) hq
  change OverBase (L := LRV) p B (q.pullback {j | U j ⊆ A})
  convert OverBase.inter hv hall hp using 1
  ext c
  change (∃ hc : c ∈ q.codes, U (q.decode ⟨c,hc⟩) ⊆ A) ↔
    (c ∈ q.codes ∧ ∀ x : Fin 1 → M,
      (∃ hc : c ∈ q.codes, x 0 ∈ U (q.decode ⟨c,hc⟩)) → x 0 ∈ A)
  exact ⟨fun ⟨hc,h⟩ => ⟨hc,fun x ⟨_,hx⟩ => h hx⟩,
    fun ⟨hc,h⟩ => ⟨hc,fun x hx => h ![x] ⟨hc,hx⟩⟩⟩

theorem classes_definable (B : FullBaseAtomicity.Base (M := M))
    (d : PuncturedBall M) (hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ d.body})
    (α : Values.Gamma (M := M)) (hα : FullGammaSyntax.Scalar B {α}) :
    FullBaseAtomicity.Family B (MaximalSubballGeometry.classes d α) := by
  let D := MaximalSubballGeometry.classes (M := M) d α
  have hR := AffineHoleGeometry.radiusClass_definable B α hα
  have hP := contained_family_definable B hd
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryBaseFamilies.Family.inter hp hR hP

/-- Every definable subset of the maximal-open-class family is finite or
cofinite. Additional named real/Gamma/ball parameters are allowed in B. -/
theorem finite_or_cofinite (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedBall M) (hd : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ d.body})
    (α : Values.Gamma (M := M)) (c : VFType (M := M))
    (hParent : d.parent = GammaRadiusAtomicity.gammaBall c α false)
    (hholes : ∀ h ∈ d.holes, ∃ b : VFType (M := M), h = GammaRadiusAtomicity.gammaBall b α true)
    {S : Set (BallImaginaries.Ball M)} (hS : FullBaseAtomicity.Family B S)
    (hST : S ⊆ MaximalSubballGeometry.classes d α) :
    S.Finite ∨ (MaximalSubballGeometry.classes d α \ S).Finite := by
  classical
  let U := BallImaginaries.underlying (M := M)
  let T := MaximalSubballGeometry.classes (M := M) d α
  let A := {x | ∃ j ∈ S, x ∈ U j}
  have hsub (j : BallImaginaries.Ball M) (hj : j ∈ T) : U j ⊆ d.body := hj.2
  have hne (j : BallImaginaries.Ball M) (_ : j ∈ T) : (U j).Nonempty :=
    encodedBall_nonempty (BallCodeGeometry.underlying_isBall j)
  have hdis := MaximalSubballGeometry.classes_disjoint δ hδ d α
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  have hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.Relation.range (ImaginaryBaseFamilies.Relation.restrict hp hS
      (OverBase.of_real (p := p) (B := B) hm))
  have hAVF : A ⊆ {x | iVF x} := by
    rintro x ⟨j,hj,hxj⟩
    exact d.body_subset_vf (hsub j (hST hj) hxj)
  have hsupport : HasFiniteBallSupport {b : Set M | IsBall b} A := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.finite_ball_support hcm hA hAVF
  obtain ⟨F,hF,hFA⟩ := hsupport
  have htest (b : Set M) (hb : b ∈ F) : d.body ⊆ b ∨ Disjoint d.body b ∨
      ∃ j ∈ T, b ∩ d.body ⊆ U j :=
    MaximalSubballGeometry.test_ball δ hδ d α c hParent hholes b (hF b hb)
  have htrace (j : BallImaginaries.Ball M) (hj : j ∈ T) (x : M) (hxj : x ∈ U j) :
      x ∈ A ↔ j ∈ S := by
    constructor
    · rintro ⟨k,hk,hxk⟩
      by_cases he : j = k
      · exact he.symm ▸ hk
      · exact (Set.disjoint_left.mp (hdis hj (hST hk) he) hxj hxk).elim
    · exact fun hjS => ⟨j,hjS,hxj⟩
  exact FiniteCofiniteClasses.finite_or_cofinite U hST hne hsub hdis F hFA htest htrace

end IntegrationInACVF.Section3ACVF.MaximalSubballFamilies
