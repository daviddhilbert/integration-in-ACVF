import IntegrationSection6.DefinableFunctionOperations
import IntegrationSection6.FamilyIntegralAddition
import IntegrationSection6.FamilyIntegralScalars

/-! The integral in Remark6.20 is a linear map on the actual semimodule
of definable RV-valued functions, with varying coefficient fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p : ℕ}

def IntegrationContext.integralLinearMap (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :
    letI := P.functionAddCommMonoid A
    letI := P.functionModule A
    P.Function A →ₗ[P.RV] P.RV := by
  letI := P.functionAddCommMonoid A
  letI := P.functionModule A
  refine { toFun := P.integral A hA, map_add' := ?_,map_smul' := ?_ }
  · intro f g
    induction f using Quotient.inductionOn with
    | h F =>
      induction g using Quotient.inductionOn with
      | h G =>
        exact (congrArg (P.integral A hA) (P.function_mk_add A F G).symm).trans
          (definableFamilyIntegral_add P A hA F G)
  · intro r f
    induction f using Quotient.inductionOn with
    | h F =>
      obtain ⟨k,U,rfl⟩ := P.rvClass_representative r
      exact (congrArg (P.integral A hA) (P.function_mk_scalar_product A F U).symm).trans
        ((definableFamilyIntegral_constant_product P A hA F U).trans (mul_comm _ _))

theorem remark_6_20_linearity (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :
    letI := P.functionAddCommMonoid A
    letI := P.functionModule A
    ∃ I : P.Function A →ₗ[P.RV] P.RV, ∀ f, I f = P.integral A hA f :=
  ⟨P.integralLinearMap A hA,fun _ => rfl⟩

end IntegrationInACVF.Section6.FiniteRV
