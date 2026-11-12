import IntegrationSection6.ContextDefinableFunctions
import IntegrationSection6.RVFamilyPadding
import IntegrationSection6.RVFamilyAdditionCoefficients

/-! Actual finite RV representatives for zero, sums and multiplication
by a constant coefficient class. Different degrees are first padded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p : ℕ}
variable {A : Set (Point (M := M) p 0)}

def DefinableRVFamily.constant {k : ℕ} (U : GammaObjectAt B Set.univ k) (A : Set (Point (M := M) p 0)) :
    DefinableRVFamily B A := ⟨rvObjectArity U.object.obj,k,constantRVSchema U p,fun x => constantRVSchema_finite U x.val.1⟩

def DefinableRVFamily.raiseTo (F : DefinableRVFamily B A) (j : ℕ) (hj : F.degree ≤ j) : DefinableRVFamily B A :=
  ⟨F.arity,j,F.schema.raiseTo hj,fun x => F.schema.finiteRow_raiseTo hj x.val.1 (F.finite x)⟩

def DefinableRVFamily.add (F G : DefinableRVFamily B A) : DefinableRVFamily B A := by
  let H := F.raiseTo (max F.degree G.degree) (le_max_left _ _)
  let I := G.raiseTo (max F.degree G.degree) (le_max_right _ _)
  exact ⟨1+(F.arity+G.arity),max F.degree G.degree,H.schema.coprodFormula I.schema,
    fun x => H.schema.finiteRow_coprod I.schema _ (fun j => (x.val.1 j).property) (H.finite x) (I.finite x)⟩

def DefinableRVFamily.product (F G : DefinableRVFamily B A) : DefinableRVFamily B A :=
  ⟨F.arity+G.arity,F.degree+G.degree,F.schema.productFormula G.schema,
    fun x => F.schema.finiteRow_product G.schema x.val.1 (F.finite x) (G.finite x)⟩

theorem definableFamilyValue_raiseTo (P : IntegrationContext B κ hs) (F : DefinableRVFamily B A)
    (j : ℕ) (hj : F.degree ≤ j) (x : A) : P.familyValue (F.raiseTo j hj) x = P.familyValue F x :=
  schemaRowCoefficient_raiseTo P hj F.schema x.val.1 (F.finite x)

theorem definableFamilyValue_add (P : IntegrationContext B κ hs) (F G : DefinableRVFamily B A) (x : A) :
    P.familyValue (F.add G) x = P.familyValue F x + P.familyValue G x := by
  exact (schemaRowCoefficient_coprod P _ _ x.val.1 _ _).trans
    (congrArg₂ (· + ·) (definableFamilyValue_raiseTo P F _ _ x) (definableFamilyValue_raiseTo P G _ _ x))

theorem definableFamilyValue_product (P : IntegrationContext B κ hs) (F G : DefinableRVFamily B A) (x : A) :
    P.familyValue (F.product G) x = P.familyValue F x * P.familyValue G x :=
  schemaRowCoefficient_product P F.schema G.schema x.val.1 (F.finite x) (G.finite x)

theorem definableFamilyValue_constant (P : IntegrationContext B κ hs) {k : ℕ} (U : GammaObjectAt B Set.univ k) (x : A) :
    P.familyValue (DefinableRVFamily.constant U A) x = P.scalarMap x.val.1 (P.rvClass U) :=
  constantRVSchema_coefficient P U x.val.1

theorem definableFamilyValue_zero (P : IntegrationContext B κ hs) (x : A) :
    P.familyValue (DefinableRVFamily.constant (gammaEmptyAt (B := B) (n := 0) (Set.subset_univ _)) A) x = 0 := by
  rw [definableFamilyValue_constant,P.rvClass_empty,map_zero]

end IntegrationInACVF.Section6
