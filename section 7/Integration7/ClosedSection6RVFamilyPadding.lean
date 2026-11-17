module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6RVFamilyProductCoefficients
public import Integration7.ClosedSection6ConstantFamilyCoefficients
public import IntegrationSection6.RVFamilyPadding
public import IntegrationSection6.RVFamilyProductCoefficients
public import IntegrationSection6.ConstantFamilyCoefficients

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
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
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a k : ℕ}

theorem schemaRowCoefficient_pad (P : IntegrationContext B κ hs) (F : GammaFiniteRVSchema B p a k)
    (x : Fin p → VF (M := M)) (hx : F.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical F.padFormula x (F.finiteRow_pad x hx) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical F x hx := by
  change schemaRowCoefficient _ _ _ _ _ _ _ _ _ _ _
    (F.productFormula (constantRVSchema (gammaPadAt (gammaUnitAt (B := B) (S := Set.univ) (Set.subset_univ _))) p)) _ _ = _
  rw [schemaRowCoefficient_product P F _ x hx (constantRVSchema_finite _ x),constantRVSchema_coefficient,P.rvClass_padding,P.rvClass_unit,map_one,mul_one]

theorem schemaRowCoefficient_raiseTo {j : ℕ} (P : IntegrationContext B κ hs) (hkj : k ≤ j)
    (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M)) (hx : F.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical (F.raiseTo hkj) x (F.finiteRow_raiseTo hkj x hx) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.canonical F x hx := by
  induction j,hkj using Nat.le_induction with
  | base => simpa only [GammaFiniteRVSchema.raiseTo,Nat.leRecOn_self]
  | succ j hj ih =>
    simpa only [F.raiseTo_succ hj] using
      (schemaRowCoefficient_pad P (F.raiseTo hj) x (F.finiteRow_raiseTo hj x hx)).trans ih

end IntegrationInACVF.Section7.CompletedSection6
