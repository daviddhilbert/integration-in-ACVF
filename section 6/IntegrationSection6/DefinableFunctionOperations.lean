import IntegrationSection6.DefinableFunctionSemimodule

/-! The transported semimodule operations are precisely pointwise
addition and scalar multiplication by the varying coefficient maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p : ℕ}

abbrev IntegrationContext.eval (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0))
    (f : P.Function A) (x : A) : (P.atVF x.val.1).RV := P.functionValue A f x

theorem IntegrationContext.functionValue_add (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0))
    (f g : P.Function A) (x : A) :
    letI := P.functionAddCommMonoid A
    P.eval A (f+g) x = P.eval A f x + P.eval A g x := by
  letI (x : A) := P.coefficientModule x.val.1
  letI := P.functionAddCommMonoid A
  exact congrArg (fun v : P.functionSubmodule A => v.val x) ((P.functionEquiv A).addEquiv.map_add f g)

theorem IntegrationContext.functionValue_smul (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0))
    (r : P.RV) (f : P.Function A) (x : A) :
    letI := P.functionAddCommMonoid A
    letI := P.functionModule A
    P.eval A (r • f) x = P.scalarMap x.val.1 r * P.eval A f x := by
  letI (x : A) := P.coefficientModule x.val.1
  letI := P.functionAddCommMonoid A
  letI := P.functionModule A
  exact congrArg (fun v : P.functionSubmodule A => v.val x) ((P.functionLinearEquiv A).map_smul r f)

theorem IntegrationContext.function_mk_add (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0))
    (F G : DefinableRVFamily B A) :
    letI := P.functionAddCommMonoid A
    (Quotient.mk _ (F.add G) : P.Function A) = Quotient.mk _ F + Quotient.mk _ G := by
  letI := P.functionAddCommMonoid A
  apply definableRVFunction_ext P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order A
  intro x
  exact (definableFamilyValue_add P F G x).trans (P.functionValue_add A (Quotient.mk _ F) (Quotient.mk _ G) x).symm

theorem IntegrationContext.function_mk_scalar_product (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0))
    (F : DefinableRVFamily B A) {k : ℕ} (U : GammaObjectAt B Set.univ k) :
    letI := P.functionAddCommMonoid A
    letI := P.functionModule A
    (Quotient.mk _ (F.product (DefinableRVFamily.constant U A)) : P.Function A) = P.rvClass U • Quotient.mk _ F := by
  letI := P.functionAddCommMonoid A
  letI := P.functionModule A
  apply definableRVFunction_ext P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
    P.value P.value_mem P.value_large P.section5_two_order A
  intro x
  exact (definableFamilyValue_product P F (DefinableRVFamily.constant U A) x).trans
    ((congrArg (fun t => P.familyValue F x * t) (definableFamilyValue_constant P U x)).trans
      ((mul_comm _ _).trans (P.functionValue_smul A (P.rvClass U) (Quotient.mk _ F) x).symm))

end IntegrationInACVF.Section6.FiniteRV
