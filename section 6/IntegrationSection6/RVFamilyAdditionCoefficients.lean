import IntegrationSection6.FamilyRowRepresentation
import IntegrationSection6.GammaSchemaCoproductRepresentation
import IntegrationSection6.ContextRVClasses

/-! Tagged coproducts represent pointwise sums in the varying coefficient
semirings, using the actual finite RV coproduct. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a b k : ℕ}

theorem schemaRowCoefficient_coprod (P : IntegrationContext B κ hs)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k) (x : Fin p → VF (M := M))
    (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order (F.coprodFormula G) x
          (F.finiteRow_coprod G _ (fun j => (x j).property) hF hG) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F x hF +
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order G x hG := by
  let U := schemaRowObject F x hF
  let V := schemaRowObject G x hG
  have hr := gammaSchemaRepresents_coprod U V F G (fun j => (x j).val) (fun j => (x j).property)
    (schemaRowObject_represents F x hF) (schemaRowObject_represents G x hG)
  exact (schemaRowCoefficient_of_represents P x (gammaCoprodAt U V) _ _ hr).trans ((P.atVF x).rvClass_coprod U V)

end IntegrationInACVF.Section6
