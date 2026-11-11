import IntegrationSection3ACVF.GammaSlopeDomain
import IntegrationSection3ACVF.GammaSlopeOutput

/-! Actual pair formulas for an RV coefficient and for a different
coefficient. All output differences are the original VF differences. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVSlopeGraph
open IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace IntegrationInACVF.Section3ACVF.RVSlopePairFormula

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem multiply_difference (c x y : VFType (M := M)) :
    multiply (iRv c.val) (difference y.val x.val) = iRv (c*(y-x)).val := by
  rw [difference_vf]
  have hm := multiply_rv (CanonicalRV.encodedRv c) (CanonicalRV.encodedRv (y-x))
  exact hm.trans (rv_mul_hom_of_model hM c.property (y-x).property).symm

theorem pair_eq (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (γ : Values.Gamma (M := M)) (d : M) (hd : RVSlopeGamma.relation A f γ d)
    (c : VFType (M := M)) (hc : iRv c.val = d)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hVal : Values.vfValueHom (y-x) = γ.val) :
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    CanonicalRV.encodedRv (fy-fx) = CanonicalRV.encodedRv (c*(y-x)) := by
  have hCoeff := GammaSlopeDomain.coefficient_for_pair B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ d hd x y hx hy hVal
  have hOut := GammaSlopeOutput.output_eq B h00 δ hδ hδ1 ho hA f hf hfVF hinj x y hx hy d hCoeff
  rw [← hc,multiply_difference] at hOut
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  rw [difference_vf fy fx] at hOut
  exact Subtype.ext hOut.symm

theorem pair_ne (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (γ : Values.Gamma (M := M)) (d : M) (hd : RVSlopeGamma.relation A f γ d)
    (c : VFType (M := M)) (hc : d ≠ iRv c.val)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hVal : Values.vfValueHom (y-x) = γ.val) :
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    CanonicalRV.encodedRv (fy-fx) ≠ CanonicalRV.encodedRv (c*(y-x)) := by
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  have hCoeff := GammaSlopeDomain.coefficient_for_pair B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ d hd x y hx hy hVal
  have hOut := GammaSlopeOutput.output_eq B h00 δ hδ hδ1 ho hA f hf hfVF hinj x y hx hy d hCoeff
  change CanonicalRV.encodedRv (fy-fx) ≠ CanonicalRV.encodedRv (c*(y-x))
  intro he
  have heRaw : difference (f y.val) (f x.val) = iRv (c*(y-x)).val :=
    (difference_vf fy fx).trans (congrArg Subtype.val he)
  have hm : multiply d (difference y.val x.val) = multiply (iRv c.val) (difference y.val x.val) :=
    hOut.trans (heRaw.trans (multiply_difference c x y).symm)
  let t : CanonicalRV.RVSort M := ⟨difference y.val x.val,hCoeff.1.1⟩
  change multiply (⟨d,hCoeff.2.1.1⟩ : CanonicalRV.RVSort M).val t.val =
    multiply (CanonicalRV.encodedRv c).val t.val at hm
  rw [multiply_rv (⟨d,hCoeff.2.1.1⟩ : CanonicalRV.RVSort M) t,
    multiply_rv (CanonicalRV.encodedRv c) t] at hm
  exact hc (rv_mul_left_cancel_of_model hM hCoeff.2.1.1 hCoeff.1.1 hCoeff.1.2
    (rv_mem hM c.property) hm)

end IntegrationInACVF.Section3ACVF.RVSlopePairFormula
