import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6IntegrationContexts
import Integration7.ClosedSection6DefinableRVFunctions
import IntegrationSection6.ContextDefinableFunctions
import IntegrationSection6.IntegrationContexts
import IntegrationSection6.DefinableRVFunctions

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}

abbrev IntegrationContext.Function (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) :=
  DefinableRVFunction P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.canonical A

abbrev IntegrationContext.functionValue (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) :=
  definableRVFunctionValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.canonical A

abbrev IntegrationContext.familyValue (P : IntegrationContext B κ hs) {p : ℕ}
    {A : Set (Point (M := M) p 0)} (F : DefinableRVFamily B A) :=
  definableRVFamilyValue P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.canonical F

abbrev IntegrationContext.integral (P : IntegrationContext B κ hs) {p : ℕ}
    (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :=
  definableFunctionIntegral P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.canonical A hA

end IntegrationInACVF.Section7.CompletedSection6
