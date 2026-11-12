import IntegrationSection6.IntegrationContexts
import IntegrationSection6.DefinableRVFunctions

/-! Context notation for the actual quotient of definable families. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}

abbrev IntegrationContext.Function (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) :=
  DefinableRVFunction P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order A

abbrev IntegrationContext.functionValue (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) :=
  definableRVFunctionValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order A

abbrev IntegrationContext.familyValue (P : IntegrationContext B κ hs) {p : ℕ}
    {A : Set (Point (M := M) p 0)} (F : DefinableRVFamily B A) :=
  definableRVFamilyValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order F

abbrev IntegrationContext.integral (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :=
  definableFunctionIntegral P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order A hA

end IntegrationInACVF.Section6.FiniteRV
