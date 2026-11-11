import IntegrationSection3ACVF.RVSlopeRigidity

/-! Lemma 3.18: actual RV-linearity on an atomic open ball. The proof
uses finite-fibre means and Gamma-linearity of a translated error map;
it does not use a piecewise-affine endpoint assertion. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVLinearity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def RVLinear (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (t : CanonicalRV.RVSort M) : Prop :=
  ∀ (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A),
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    iRv (fy-fx).val = iRVMul t.val (iRv (y-x).val)

theorem ordinary_lift {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    ∃ c : VFType (M := M), c ≠ 0 ∧
      ∀ (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true) (hy : y.val ∈ gammaBall a α true),
        let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
        let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
        CanonicalRV.encodedRv (fy-fx) = CanonicalRV.encodedRv (c*(y-x)) := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  obtain ⟨hat,hopen⟩ := RVInverse.atomic_open_image B h00 δ hδ hδ1 ho hA f hf hfVF hinj
  rcases hopen with hVF | ⟨b,β,hImage⟩
  · exact (OpenBallConstancy.atomic_not_contains_vf B hat (hVF.symm ▸ Set.Subset.rfl)).elim
  · have hLin := GammaLinearity.ordinary hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage
    obtain ⟨γ,hαγ⟩ := exists_gt α
    obtain ⟨d,hd⟩ := (GammaSlopeDomain.domain_iff a α γ f hfVF hinj).mpr hαγ
    have hd0 : NonzeroRV d := by
      obtain ⟨t,_,ht⟩ := hd
      exact ht.2.1
    obtain ⟨c,hcRV⟩ := CanonicalRV.encodedRv_surjective (⟨d,hd0.1⟩ : CanonicalRV.RVSort M)
    have hc : iRv c.val = d := congrArg Subtype.val hcRV
    have hcNZ : c ≠ 0 := by
      intro hz
      have hrz := (CanonicalRV.encodedRv_zero_iff c).mpr hz
      exact hd0.2 (hc.symm.trans hrz)
    have hAll (η : Values.Gamma (M := M)) (e : M)
        (he : RVSlopeGamma.relation (gammaBall a α true) f η e) : d = e := by
      rcases lt_trichotomy γ η with h | h | h
      · exact RVSlopeRigidity.ordered_coefficients_eq hκ hs B hsmall h00 δ hδ hδ1 a α hA
          f hf hfVF hinj (β/α) hLin γ η h d e hd he
      · subst η
        exact RVSlopeConstancy.on_value_fibre B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ hd he
      · exact (RVSlopeRigidity.ordered_coefficients_eq hκ hs B hsmall h00 δ hδ hδ1 a α hA
          f hf hfVF hinj (β/α) hLin η γ h e d he hd).symm
    refine ⟨c,hcNZ,?_⟩
    intro x y hx hy
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    change CanonicalRV.encodedRv (fy-fx) = CanonicalRV.encodedRv (c*(y-x))
    by_cases hxy : y = x
    · subst y
      have heq : fy = fx := rfl
      rw [heq,sub_self,sub_self,mul_zero]
    · have hValNZ : Values.vfValueHom (y-x) ≠ Values.infinity := by
        intro hi
        have hr0 := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp hi
        exact (sub_ne_zero.mpr hxy) ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hr0)
      let η : Values.Gamma (M := M) := ⟨Values.vfValueHom (y-x),hValNZ⟩
      have hαη : α < η := GammaDifferenceRealization.difference_gt_radius a α x y hx hy
      obtain ⟨e,he⟩ := (GammaSlopeDomain.domain_iff a α η f hfVF hinj).mpr hαη
      exact RVSlopePairFormula.pair_eq B h00 δ hδ hδ1 ho hA f hf hfVF hinj η e he c
        (hc.trans (hAll η e he)) x y hx hy rfl

theorem ordinary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    ∃ t : CanonicalRV.RVSort M, t.val ≠ iRVZero ∧ RVLinear (gammaBall a α true) f hfVF t := by
  obtain ⟨c,hc,hLin⟩ := ordinary_lift hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj
  refine ⟨CanonicalRV.encodedRv c,fun h => hc ((CanonicalRV.encodedRv_zero_iff c).mp h),?_⟩
  intro x y hx hy
  exact (congrArg Subtype.val (hLin x y hx hy)).trans
    (rv_mul_hom_of_model hM c.property (y-x).property)

theorem lemma_3_18 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A) :
    ∃ t : CanonicalRV.RVSort M, t.val ≠ iRVZero ∧ RVLinear A f hfVF t := by
  rcases ho with hVF | ⟨a,α,rfl⟩
  · exact (OpenBallConstancy.atomic_not_contains_vf B hA (hVF.symm ▸ Set.Subset.rfl)).elim
  · exact ordinary hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj

end IntegrationInACVF.Section3ACVF.RVLinearity
