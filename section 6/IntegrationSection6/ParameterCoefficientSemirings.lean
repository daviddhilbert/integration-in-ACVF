import IntegrationSection6.VFParameterCoefficientBases
import IntegrationSection6.GlobalIntegrationCharacterization

/-! The varying coefficient semirings in6.20 are the actual RV/Isp
semirings over dcl(B,x), with the6.19 equivalence available in each fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
variable (FBase : VFFieldBase B.real) (hB : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

abbrev ParameterCoefficientSemiring (x : Fin p → VF (M := M)) :=
  GlobalIntegrationSemiringTarget (B := vfParameterCoefficientBase B x) hκ hs h00
    (vfParameterCoefficientBase_real_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    (vfParameterCoefficientBase_field x)
    (vfParameterCoefficientBase_gamma_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    δ (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 h58 (vfParameterCoefficientBase_generated hB x)

def parameterVFCommSemiring (x : Fin p → VF (M := M)) :
    CommSemiring (GammaVFAllAdditiveKPlus (vfParameterCoefficientBase B x)) :=
  gammaVFAllCommSemiring hκ hs h00
    (vfParameterCoefficientBase_real_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    (vfParameterCoefficientBase_field x)
    (vfParameterCoefficientBase_gamma_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    δ (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 h58 (vfParameterCoefficientBase_generated hB x)

def parameterIntegralEquiv (x : Fin p → VF (M := M)) :
    letI := parameterVFCommSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x
    GammaVFAllAdditiveKPlus (vfParameterCoefficientBase B x) ≃+*
      ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x :=
  theorem_6_19 hκ hs h00
    (vfParameterCoefficientBase_real_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    (vfParameterCoefficientBase_field x)
    (vfParameterCoefficientBase_gamma_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    δ (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 h58 (vfParameterCoefficientBase_generated hB x)

end IntegrationInACVF.Section6.FiniteRV
