import IntegrationSection3ACVF.GammaLinearity

/-! Every actual RV slope has the value of the checked Gamma-linear
coefficient, and any VF representative has that same value. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVLinearitySlopeValues

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem coefficient_value (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (s : Values.Gamma (M := M)) (hLinear : GammaLinearity.GammaLinear (gammaBall a α true) f hfVF s)
    (γ : Values.Gamma (M := M)) (c : M) (hc : RVSlopeGamma.relation (gammaBall a α true) f γ c) :
    codeValue c = s := by
  have hαγ := (GammaSlopeDomain.domain_iff a α γ f hfVF hinj).mp ⟨c,hc⟩
  obtain ⟨x,y,hx,hy,_,hVal⟩ := GammaDifferenceRealization.exists_pair a α γ hαγ
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hV := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ c hc x y hx hy hVal
  have hS := hLinear x y hx hy
  rw [hVal] at hS
  have he := hV.symm.trans hS
  rw [Values.gamma_val_mul,mul_comm γ.val] at he
  have hNZ : γ.val ≠ 0 := by simpa only [← Values.infinity_eq_zero] using γ.property
  exact Subtype.ext (mul_right_cancel₀ hNZ he)

theorem lift_value (s : Values.Gamma (M := M)) (c : M) (hc : NonzeroRV c)
    (hValue : codeValue c = s) (r : VFType (M := M)) (hr : iRv r.val = c) :
    Values.vfValueHom r = s.val ∧ r ≠ 0 := by
  have hCode : (codeValue c).val = Values.vrv (⟨c,hc.1⟩ : CanonicalRV.RVSort M) := by
    simp only [codeValue,dite_eq_left hc]
    rfl
  have hRv : CanonicalRV.encodedRv r = (⟨c,hc.1⟩ : CanonicalRV.RVSort M) := Subtype.ext hr
  have hv : Values.vfValueHom r = s.val :=
    (congrArg Values.vrv hRv).trans (hCode.symm.trans (congrArg Subtype.val hValue))
  refine ⟨hv,?_⟩
  intro hz
  have hi : Values.vfValueHom r = Values.infinity := by
    rw [hz,map_zero]
    exact Values.infinity_eq_zero.symm
  exact s.property (hv.symm.trans hi)

end IntegrationInACVF.Section3ACVF.RVLinearitySlopeValues
