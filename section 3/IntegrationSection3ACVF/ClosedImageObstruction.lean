import IntegrationSection3ACVF.GammaPairFormula
import IntegrationSection3ACVF.BallCentreElimination
import IntegrationSection3ACVF.PolynomialSeparation
import IntegrationSection3ACVF.PolynomialEscape
import IntegrationSection3ACVF.PrimitiveImages

/-! Closed-image obstruction from one named source ball. The original
base contains Gamma names only; a chosen field centre never enters it. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.ClosedImageObstruction

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem with_definable_subgroup (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    (i : BallImaginaries.Ball M) (c : VFType (M := M))
    (hi : BallImaginaries.underlying i = cosetBody H c)
    (hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hO : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i))
    {A : Set M} (hA : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) A) (hAinf : A.Infinite) :
    ¬ PaperBalls.IsClosedBall A := by
  classical
  let C := B.adjoin (Sum.inl i)
  let E := vfParameterField (M := M) B.real
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
  intro hClosed
  rcases hClosed with hVF | ⟨a,ha⟩ | ⟨a,α,ha⟩
  · exact OpenBallConstancy.atomic_not_contains_vf C hA (hVF.symm ▸ Set.Subset.rfl)
  · apply hAinf
    rw [ha]
    exact Set.finite_singleton _
  · have hαinf : α.val < Values.infinity :=
      lt_of_le_of_ne (Values.le_infinity α.val) α.property
    have hTarget : (PaperBalls.IsClosedBall A ∧
        ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius A r ∧
          r < (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M))) ∨
        ∃ d : PuncturedGeometry.PuncturedBall M, PaperBalls.IsThinAnnulus d ∧ d.body = A :=
      Or.inl ⟨Or.inr (Or.inr ⟨a,α,ha⟩),↑α.val,
        Or.inr (Or.inr ⟨a,α,false,ha,rfl⟩),WithBot.coe_lt_coe.mpr hαinf⟩
    obtain ⟨G,hG,hGA⟩ := BallCentreElimination.adjoin_elimination B H hH i c hi hA.1
    obtain ⟨T,hT,p,ψ,hqf,hws,hcoeff,hψ⟩ := GammaPairFormula.presentation B hOnly G hG
    have hc : c.val ∈ BallImaginaries.underlying i := by
      rw [hi]
      exact (GammaCosetGeometry.cosetBody_mem H c c).mpr rfl
    have haA : a.val ∈ A := by
      rw [ha]
      exact BallEnlargementGeometry.gammaBall_centre_mem a α false
    let polys := MultivariatePolynomialSupport.formula p E hcoeff ψ
    let specialized (q : MvPolynomial (Fin 2) E) : Polynomial (VFType (M := M)) :=
      PolynomialSpecialization.specialize
        ((BivariateCoordinates.equiv E q).map (Polynomial.mapRingHom E.subtype)) c
    let F := polys.toFinset.image specialized
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
    have hnt := (ValOneEC.Johnson.exists_ne_zero_val_lt_one_iff v).mpr
      (CanonicalBallSupport.valuation_nontrivial v hv δ hδ1)
    have hroots (P : Polynomial (VFType (M := M))) (hP : P ∈ F)
        (x : VFType (M := M)) (hx : x ∈ P.roots) : ¬ v (x-a) ≤ v r := by
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
      by_cases hq0 : q = 0
      · simp [specialized,hq0,PolynomialSpecialization.specialize] at hx
      · intro hxin
        have hxA : x.val ∈ A := by
          rw [ha]
          exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr x).mpr hxin
        have hne := PolynomialSeparation.nonzero_on_product C h00 δ hδC hδ1
          hOpen hO hA hTarget q hq0 x c hxA hc
        have hz : (specialized q).eval x = 0 := Polynomial.isRoot_of_mem_roots hx
        change (PolynomialSpecialization.specialize
          ((BivariateCoordinates.equiv E q).map (Polynomial.mapRingHom E.subtype)) c).eval x = 0 at hz
        rw [BivariateCoordinates.eval₂_coordinates] at hz
        exact hne hz
    obtain ⟨d,hd,hRV⟩ := PolynomialEscape.finite_polynomial_escape v hv hnt F a r hroots
    have hSupport (q : MvPolynomial (Fin 2) E) (hq : q ∈ polys) :
        iRv (q.eval₂ E.subtype ![d,c]).val = iRv (q.eval₂ E.subtype ![a,c]).val := by
      have hmem : specialized q ∈ F := Finset.mem_image.mpr
        ⟨q,List.mem_toFinset.mpr hq,rfl⟩
      have he := hRV (specialized q) hmem
      change iRv ((PolynomialSpecialization.specialize
          ((BivariateCoordinates.equiv E q).map (Polynomial.mapRingHom E.subtype)) c).eval d).val =
        iRv ((PolynomialSpecialization.specialize
          ((BivariateCoordinates.equiv E q).map (Polynomial.mapRingHom E.subtype)) c).eval a).val at he
      simpa only [BivariateCoordinates.eval₂_coordinates] using he
    have hvalues (x y : VFType (M := M)) : vfValues ![x,y] = ![x.val,y.val] := by
      funext j
      fin_cases j <;> rfl
    have hψa : ψ.Realize p.values (vfValues ![a,c]) := by
      rw [hvalues]
      exact (hψ a c).mpr ((hGA c.val hc a.val).mpr haA)
    have hψd := (MultivariatePolynomialSupport.formula_iff_of_support p E hcoeff ψ hqf hws
      ![d,c] ![a,c] hSupport).mpr hψa
    rw [hvalues] at hψd
    have hdA : d.val ∈ A := (hGA c.val hc d.val).mp ((hψ d c).mp hψd)
    apply hd
    rw [ha] at hdA
    exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr d).mp hdA

theorem not_closed (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ j ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), j = Sum.inr γ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (i : BallImaginaries.Ball M) (hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hO : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i))
    {A : Set M} (hA : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) A) (hAinf : A.Infinite) :
    ¬ PaperBalls.IsClosedBall A := by
  rcases hOpen with hVF | ⟨c,σ,hball⟩
  · exact (OpenBallConstancy.atomic_not_contains_vf (B.adjoin (Sum.inl i)) hO
      (hVF.symm ▸ Set.Subset.rfl)).elim
  · let C := B.adjoin (Sum.inl i)
    let Bσ := B.adjoin (Sum.inr σ)
    have hδC : FullGammaSyntax.Scalar C {δ} :=
      FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
    have hδσ : FullGammaSyntax.Scalar Bσ {δ} :=
      FullBaseAtomicity.OverBase.mono hδ Set.Subset.rfl (Set.subset_insert _ _)
    have hσ : FullGammaSyntax.Scalar Bσ {σ} := AdjoinGamma.named_scalar σ (Set.mem_insert _ _)
    have hcomm : C.adjoin (Sum.inr σ) = Bσ.adjoin (Sum.inl i) := by
      exact congrArg (fun S : Set (ParameterPresentation.Name (M := M)) =>
        (⟨B.real,S⟩ : FullBaseAtomicity.Base (M := M))) (Set.insert_comm _ _ _)
    have hOσ0 := FullGammaAtomicity.lemma_3_3_one_unary h00 C δ hδC hδ1 hO σ
    have hAσ0 := FullGammaAtomicity.lemma_3_3_one_unary h00 C δ hδC hδ1 hA σ
    have hOσ : AdjoinBall.AtomicOver (Bσ.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
      rw [← hcomm]
      exact hOσ0
    have hAσ : AdjoinBall.AtomicOver (Bσ.adjoin (Sum.inl i)) A := by
      rw [← hcomm]
      exact hAσ0
    have hOnlyσ : ∀ j ∈ Bσ.imaginary, ∃ γ : Values.Gamma (M := M), j = Sum.inr γ := by
      intro j hj
      rcases hj with rfl | hj
      · exact ⟨σ,rfl⟩
      · exact hOnly j hj
    obtain ⟨H,hH,hBody⟩ := FullGammaRadius.gamma_subgroup Bσ σ hσ true
    have hi : BallImaginaries.underlying i = cosetBody H c := hball.trans (hBody c).symm
    exact with_definable_subgroup Bσ hOnlyσ h00 δ hδσ hδ1 H hH i c hi
      (Or.inr ⟨c,σ,hball⟩) hOσ hAσ hAinf

theorem lemma_3_14 (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ j ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), j = Sum.inr γ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (i : BallImaginaries.Ball M) (hOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying i))
    (hO : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i))
    {A : Set M} (hA : AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) A) (hAinf : A.Infinite)
    (hOne : PrimitiveImages.OnePrimitiveComponent A) : ¬ PaperBalls.IsClosedBall A :=
  not_closed B hOnly h00 δ hδ hδ1 i hOpen hO hA hAinf

end IntegrationInACVF.Section3ACVF.ClosedImageObstruction
