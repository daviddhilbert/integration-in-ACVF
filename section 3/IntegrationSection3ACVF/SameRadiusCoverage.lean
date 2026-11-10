import IntegrationSection3ACVF.FullGammaAtomicity
import IntegrationSection3ACVF.FullGammaRadius
import IntegrationSection3ACVF.PaperBallInvariants
import IntegrationSection3.ClassCoverage

/-! Corollary 3.7 from Gamma-atomicity and definable coset coverage.
No primitive decomposition theorem is assumed. Adjoining the radius is
justified by the already checked Lemma 3.3; the original base is retained
in the hypotheses and no centre is named there. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.SameRadiusCoverage

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem corollary_3_7_gamma (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hAtomic : AdjoinBall.AtomicOver B A)
    (a : VFType (M := M)) (γ : Values.Gamma (M := M)) (strict : Bool)
    (hsub : gammaBall a γ strict ⊆ A) :
    ∀ x : VFType (M := M), x.val ∈ A →
      x.val ∈ gammaBall x γ strict ∧ gammaBall x γ strict ⊆ A := by
  let C := B.adjoin (Sum.inr γ)
  have hAC : AdjoinBall.AtomicOver C A :=
    FullGammaAtomicity.lemma_3_3_one_unary h00 B δ hδ hδ1 hAtomic γ
  have hγ : FullGammaSyntax.Scalar C {γ} := AdjoinGamma.named_scalar γ (by
    change Sum.inr γ ∈ insert (Sum.inr γ) B.imaginary
    exact Set.mem_insert _ _)
  obtain ⟨H,hH,hballs⟩ := FullGammaRadius.gamma_subgroup C γ hγ strict
  let R := cosetRelation H
  have hR := FullBallCoset.cosetRelation_definable C H hH
  have hf (x : VFType (M := M)) : {y | (x.val,y) ∈ R} = gammaBall x γ strict :=
    (cosetRelation_fibre H x).trans (hballs x)
  have hcentre (x : VFType (M := M)) : x.val ∈ gammaBall x γ strict := by
    rw [← hballs x]
    exact ⟨x,rfl,rfl⟩
  have hw : a.val ∈ ClassCoverage.wholeClass R A :=
    fun y hy => hsub ((Set.ext_iff.mp (hf a) y).mp hy)
  have hp := ParameterPresentation.codeDomain_definable (M := M) C.real
  let p := @ParameterPresentation.presentation M sM hM
  have hall : A ⊆ ClassCoverage.wholeClass R A := by
    letI := CanonicalStructure.normalize (M := M)
    exact ClassCoverage.complete_type_cover hp hAC.1 hAC.2 hR
      ⟨a.val,hsub (hcentre a),hw⟩
  intro x hx
  refine ⟨hcentre x,fun y hy => ?_⟩
  exact hall hx y ((Set.ext_iff.mp (hf x) y).mpr hy)

theorem corollary_3_7_open (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A O : Set M} (hAtomic : AdjoinBall.AtomicOver B A)
    (ho : PaperBalls.IsOpenBall O) {r : PaperBalls.Radius (M := M)}
    (hr : PaperBalls.HasRadius O r) (hsub : O ⊆ A) :
    ∀ x : VFType (M := M), x.val ∈ A → ∃ D : Set M,
      PaperBalls.IsOpenBall D ∧ PaperBalls.HasRadius D r ∧ D ⊆ A ∧ x.val ∈ D := by
  rcases ho with rfl | ⟨a,γ,rfl⟩
  · exact fun x _ => ⟨{y | iVF y},Or.inl rfl,hr,hsub,x.property⟩
  · have he : r = (↑γ.val : PaperBalls.Radius (M := M)) :=
      PaperBallInvariants.hasRadius_unique δ hδ1 hr (Or.inr (Or.inr ⟨a,γ,true,rfl,rfl⟩))
    intro x hx
    have hc := corollary_3_7_gamma h00 B δ hδ hδ1 hAtomic a γ true hsub x hx
    refine ⟨gammaBall x γ true,Or.inr ⟨x,γ,rfl⟩,?_,hc.2,hc.1⟩
    rw [he]
    exact Or.inr (Or.inr ⟨x,γ,true,rfl,rfl⟩)

theorem corollary_3_7_closed (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A O : Set M} (hAtomic : AdjoinBall.AtomicOver B A)
    (ho : PaperBalls.IsClosedBall O) {r : PaperBalls.Radius (M := M)}
    (hr : PaperBalls.HasRadius O r) (hsub : O ⊆ A) :
    ∀ x : VFType (M := M), x.val ∈ A → ∃ D : Set M,
      PaperBalls.IsClosedBall D ∧ PaperBalls.HasRadius D r ∧ D ⊆ A ∧ x.val ∈ D := by
  rcases ho with rfl | ⟨a,rfl⟩ | ⟨a,γ,rfl⟩
  · exact fun x _ => ⟨{y | iVF y},Or.inl rfl,hr,hsub,x.property⟩
  · have he : r = (↑(Values.infinity (M := M)) : PaperBalls.Radius (M := M)) :=
      PaperBallInvariants.hasRadius_unique δ hδ1 hr (Or.inr (Or.inl ⟨a,rfl,rfl⟩))
    intro x hx
    refine ⟨{x.val},Or.inr (Or.inl ⟨x,rfl⟩),?_,?_,Set.mem_singleton _⟩
    · rw [he]
      exact Or.inr (Or.inl ⟨x,rfl,rfl⟩)
    · rintro y rfl
      exact hx
  · have he : r = (↑γ.val : PaperBalls.Radius (M := M)) :=
      PaperBallInvariants.hasRadius_unique δ hδ1 hr (Or.inr (Or.inr ⟨a,γ,false,rfl,rfl⟩))
    intro x hx
    have hc := corollary_3_7_gamma h00 B δ hδ hδ1 hAtomic a γ false hsub x hx
    refine ⟨gammaBall x γ false,Or.inr (Or.inr ⟨x,γ,rfl⟩),?_,hc.2,hc.1⟩
    rw [he]
    exact Or.inr (Or.inr ⟨x,γ,false,rfl,rfl⟩)

end IntegrationInACVF.Section3ACVF.SameRadiusCoverage
