import IntegrationSection3ACVF.GammaDifferenceRealization

/-! The domain of the descended slope relation for an ordinary open
ball is exactly the actual Gamma tail above its radius. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.GammaSlopeDomain

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem domain_iff (a : VFType (M := M)) (α γ : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) :
    (∃ c : M, RVSlopeGamma.relation (gammaBall a α true) f γ c) ↔ α < γ := by
  constructor
  · rintro ⟨c,t,htγ,ht⟩
    obtain ⟨_,_,x,hx,y,hy,htInput,_⟩ := ht
    let xx : VFType (M := M) := ⟨x,hx.1⟩
    let yy : VFType (M := M) := ⟨y,hy.1⟩
    have htRV : t = CanonicalRV.encodedRv (yy-xx) :=
      Subtype.ext (htInput.trans (difference_vf yy xx))
    have he : Values.vfValueHom (yy-xx) = γ.val := (congrArg Values.vrv htRV).symm.trans htγ
    have hl := GammaDifferenceRealization.difference_gt_radius a α xx yy hx hy
    have hαγ : α.val < γ.val := he ▸ hl
    exact hαγ
  · intro hαγ
    obtain ⟨x,y,hx,hy,hne,hval⟩ := GammaDifferenceRealization.exists_pair a α γ hαγ
    obtain ⟨c,hc⟩ := RVSlopeFibres.slope_of_pair f hfVF hinj x y hx hy hne
    refine ⟨c.val,CanonicalRV.encodedRv (y-x),hval,?_⟩
    change ![iRv (y-x).val,c.val] ∈ slopes (gammaBall a α true) f
    simpa only [difference_vf] using hc

theorem coefficient_for_pair (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (γ : Values.Gamma (M := M)) (c : M) (hc : RVSlopeGamma.relation A f γ c)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hval : Values.vfValueHom (y-x) = γ.val) :
    ![difference y.val x.val,c] ∈ slopes A f := by
  have hr0 : y-x ≠ 0 := by
    intro h
    have hz : Values.vfValueHom (y-x) = Values.infinity := by
      rw [h,map_zero]
      exact Values.infinity_eq_zero.symm
    exact γ.property (hval.symm.trans hz)
  obtain ⟨d,hd⟩ := RVSlopeFibres.slope_of_pair f hfVF hinj x y hx hy (sub_ne_zero.mp hr0)
  have hdγ : RVSlopeGamma.relation A f γ d.val := by
    refine ⟨CanonicalRV.encodedRv (y-x),hval,?_⟩
    change ![iRv (y-x).val,d.val] ∈ slopes A f
    simpa only [difference_vf] using hd
  have he : d.val = c := RVSlopeConstancy.on_value_fibre B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ hdγ hc
  rwa [he] at hd

end IntegrationInACVF.Section3ACVF.GammaSlopeDomain
