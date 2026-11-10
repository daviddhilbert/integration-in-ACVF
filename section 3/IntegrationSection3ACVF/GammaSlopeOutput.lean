import IntegrationSection3ACVF.GammaSlopeDomain

/-! The actual output valuation equals the input valuation multiplied
by the Gamma value of its unique RV coefficient. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.GammaSlopeOutput

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem output_eq (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (c : M) (hc : ![difference y.val x.val,c] ∈ slopes A f) :
    multiply c (difference y.val x.val) = difference (f y.val) (f x.val) := by
  obtain ⟨_,_,u,hu,v,hv,ht,hs⟩ := hc
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with h | ⟨a,α,h⟩
    · exact h ▸ Set.Subset.rfl
    · rw [h]
      intro z hz
      exact hz.1
  have he := RVMapRelation.right_unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    x y ⟨u,hAVF hu⟩ ⟨v,hAVF hv⟩ hx hy hu hv ht
  exact hs.trans he.symm

theorem pair_output_value (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (γ : Values.Gamma (M := M)) (c : M) (hc : RVSlopeGamma.relation A f γ c)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hγr : Values.vfValueHom (y-x) = γ.val) :
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    Values.vfValueHom (fy-fx) = (γ*codeValue c).val := by
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  let b : VFType (M := M) := fy-fx
  let r : VFType (M := M) := y-x
  change Values.vfValueHom b = (γ*codeValue c).val
  have hCoeff := GammaSlopeDomain.coefficient_for_pair B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    γ c hc x y hx hy hγr
  have hcNZ : NonzeroRV c := hCoeff.2.1
  let C : CanonicalRV.RVSort M := ⟨c,hcNZ.1⟩
  have hmul := output_eq B h00 δ hδ hδ1 ho hA f hf hfVF hinj x y hx hy c hCoeff
  have hinput : difference y.val x.val = iRv r.val := difference_vf y x
  have houtput : difference (f y.val) (f x.val) = iRv b.val := difference_vf fy fx
  have hraw : iRVMul c (iRv r.val) = iRv b.val := calc
    iRVMul c (iRv r.val) = multiply c (iRv r.val) := (multiply_rv C (CanonicalRV.encodedRv r)).symm
    _ = multiply c (difference y.val x.val) := congrArg (multiply c) hinput.symm
    _ = difference (f y.val) (f x.val) := hmul
    _ = iRv b.val := houtput
  have hRV : (⟨iRVMul c (iRv r.val),rv_mul_mem hM C.property (CanonicalRV.encodedRv r).property⟩ :
      CanonicalRV.RVSort M) = CanonicalRV.encodedRv b := Subtype.ext hraw
  have hv : Values.vfValueHom b = Values.vrv C * Values.vfValueHom r :=
    (congrArg Values.vrv hRV).symm.trans (Values.vrv_mul C (CanonicalRV.encodedRv r))
  have hcode : (codeValue c).val = Values.vrv C := by
    simp only [codeValue,dite_eq_left hcNZ]
    rfl
  calc
    Values.vfValueHom b = Values.vrv C * Values.vfValueHom r := hv
    _ = (codeValue c).val * γ.val := by rw [← hcode,hγr]
    _ = γ.val * (codeValue c).val := mul_comm _ _
    _ = (γ*codeValue c).val := (Values.gamma_val_mul γ (codeValue c)).symm

end IntegrationInACVF.Section3ACVF.GammaSlopeOutput
