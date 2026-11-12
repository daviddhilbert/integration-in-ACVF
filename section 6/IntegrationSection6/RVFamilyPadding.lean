import IntegrationSection6.RVFamilyProductCoefficients
import IntegrationSection6.ConstantFamilyCoefficients

/-! Zero-volume padding raises the finite RV degree while leaving the
represented coefficient unchanged. No bound on the whole domain is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p a k : ℕ}

def GammaFiniteRVSchema.padFormula (F : GammaFiniteRVSchema B p a k) : GammaFiniteRVSchema B p a (k+1) :=
  F.productFormula (constantRVSchema (gammaPadAt (gammaUnitAt (B := B) (S := Set.univ) (Set.subset_univ _))) p)

theorem GammaFiniteRVSchema.finiteRow_pad (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) : F.padFormula.finiteRow (fun j => (x j).val) :=
  F.finiteRow_product _ x hx (constantRVSchema_finite _ x)

theorem schemaRowCoefficient_pad (P : IntegrationContext B κ hs) (F : GammaFiniteRVSchema B p a k)
    (x : Fin p → VF (M := M)) (hx : F.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F.padFormula x (F.finiteRow_pad x hx) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F x hx := by
  change schemaRowCoefficient _ _ _ _ _ _ _ _ _ _ _ (F.productFormula _) _ _ = _
  rw [schemaRowCoefficient_product P F _ x hx (constantRVSchema_finite _ x),constantRVSchema_coefficient,P.rvClass_padding,P.rvClass_unit,map_one,mul_one]

def GammaFiniteRVSchema.raiseTo {j : ℕ} (hkj : k ≤ j) (F : GammaFiniteRVSchema B p a k) : GammaFiniteRVSchema B p a j :=
  Nat.leRecOn (C := fun t => GammaFiniteRVSchema B p a t) hkj (fun G => G.padFormula) F

theorem GammaFiniteRVSchema.raiseTo_refl (F : GammaFiniteRVSchema B p a k) : F.raiseTo (Nat.le_refl k) = F :=
  Nat.leRecOn_self (C := fun t => GammaFiniteRVSchema B p a t) F

theorem GammaFiniteRVSchema.raiseTo_succ {j : ℕ} (hkj : k ≤ j) (F : GammaFiniteRVSchema B p a k) :
    F.raiseTo (hkj.trans (Nat.le_succ j)) = (F.raiseTo hkj).padFormula := Nat.leRecOn_succ (C := fun t => GammaFiniteRVSchema B p a t) hkj F

theorem GammaFiniteRVSchema.finiteRow_raiseTo {j : ℕ} (hkj : k ≤ j) (F : GammaFiniteRVSchema B p a k)
    (x : Fin p → VF (M := M)) (hx : F.finiteRow (fun j => (x j).val)) :
    (F.raiseTo hkj).finiteRow (fun j => (x j).val) := by
  induction j,hkj using Nat.le_induction with
  | base => simpa only [F.raiseTo_refl] using hx
  | succ j hj ih => simpa only [F.raiseTo_succ hj] using (F.raiseTo hj).finiteRow_pad x ih

theorem schemaRowCoefficient_raiseTo {j : ℕ} (P : IntegrationContext B κ hs) (hkj : k ≤ j)
    (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M)) (hx : F.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order (F.raiseTo hkj) x (F.finiteRow_raiseTo hkj x hx) =
      schemaRowCoefficient P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
        P.value P.value_mem P.value_large P.section5_two_order F x hx := by
  induction j,hkj using Nat.le_induction with
  | base => simpa only [GammaFiniteRVSchema.raiseTo,Nat.leRecOn_self]
  | succ j hj ih =>
    simpa only [F.raiseTo_succ hj] using
      (schemaRowCoefficient_pad P (F.raiseTo hj) x (F.finiteRow_raiseTo hj x hx)).trans ih

end IntegrationInACVF.Section6
