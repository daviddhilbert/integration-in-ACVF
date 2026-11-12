import IntegrationSection6.RVFamilyProducts
import IntegrationSection6.FamilyRowRepresentation
import IntegrationSection6.ContextRVClasses
import IntegrationSection6.GammaProductLifts

/-! Product families have exactly the product of the two coefficient
classes in the actual parameter-dependent semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a b k l : ℕ}

theorem schemaRowLift_product (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M)) :
    schemaRowLift (F.productFormula G) x = mixedProductSet (schemaRowLift F x) (schemaRowLift G x) := by
  ext q
  exact F.product_row_volume G x q.2 (tupleRV q.1)

theorem schemaRowCoefficient_product (P : IntegrationContext B κ hs)
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l) (x : Fin p → VF (M := M))
    (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order (F.productFormula G) x (F.finiteRow_product G x hF hG) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F x hF *
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order G x hG := by
  let U := schemaRowObject F x hF
  let V := schemaRowObject G x hG
  let W := schemaRowObject (F.productFormula G) x (F.finiteRow_product G x hF hG)
  have he : W.toGamma.lift = (gammaProductAt U V).toGamma.lift := by
    exact (schemaRowObject_lift (F.productFormula G) x _).trans
      ((schemaRowLift_product F G x).trans
        ((congrArg₂ mixedProductSet (schemaRowObject_lift F x hF).symm (schemaRowObject_lift G x hG).symm).trans
          (gammaProductAt_lift U V).symm))
  have hc : (P.atVF x).rvClass W = (P.atVF x).rvClass (gammaProductAt U V) :=
    (rvGlobalIntegralClass_eq_iff_liftIso (P.atVF x).countable_le hs (P.atVF x).characteristic
      (P.atVF x).real_small (P.atVF x).field_base (P.atVF x).gamma_small (P.atVF x).value
      (P.atVF x).value_mem (P.atVF x).value_large (P.atVF x).section5_two_order (P.atVF x).generated W _).mpr
      ⟨(gammaIso_reflexive W.toGamma.lift W.toGamma.toGammaRVObject.lift_definable).congr rfl he⟩
  exact hc.trans ((P.atVF x).rvClass_product U V)

end IntegrationInACVF.Section6
