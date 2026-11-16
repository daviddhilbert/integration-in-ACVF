module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6FamilyRowRepresentation
public import Integration7.ClosedSection6ContextRVClasses
public import IntegrationSection6.RVFamilyAdditionCoefficients
public import IntegrationSection6.FamilyRowRepresentation
public import IntegrationSection6.GammaSchemaCoproductRepresentation
public import IntegrationSection6.ContextRVClasses

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a b k : ℕ}

theorem schemaRowCoefficient_coprod (P : IntegrationContext B κ hs)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k) (x : Fin p → VF (M := M))
    (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical (F.coprodFormula G) x
          (F.finiteRow_coprod G _ (fun j => (x j).property) hF hG) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical F x hF +
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical G x hG := by
  let U := schemaRowObject F x hF
  let V := schemaRowObject G x hG
  have hr := gammaSchemaRepresents_coprod U V F G (fun j => (x j).val) (fun j => (x j).property)
    (schemaRowObject_represents F x hF) (schemaRowObject_represents G x hG)
  exact (schemaRowCoefficient_of_represents P x (gammaCoprodAt U V) _ _ hr).trans ((P.atVF x).rvClass_coprod U V)

end IntegrationInACVF.Section7.CompletedSection6
