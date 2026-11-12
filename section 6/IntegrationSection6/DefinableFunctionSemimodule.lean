import IntegrationSection6.DefinableFamilyOperations
import IntegrationSection6.RVClassRepresentatives
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.TransferInstance

/-! The actual definable functions form the submodule of all varying
coefficient functions represented by finite Gamma RV families. Evaluation
identifies the earlier quotient with this submodule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {p : ℕ}

@[instance_reducible] def IntegrationContext.coefficientModule (P : IntegrationContext B κ hs)
    (x : Fin p → VF (M := M)) : Module P.RV (P.atVF x).RV := (P.scalarMap x).toModule

def IntegrationContext.functionSubmodule (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0)) :
    letI (x : A) := P.coefficientModule x.val.1
    Submodule P.RV (∀ x : A, (P.atVF x.val.1).RV) := by
  letI (x : A) := P.coefficientModule x.val.1
  refine { carrier := Set.range (fun F : DefinableRVFamily B A => P.familyValue F)
           add_mem' := fun {f g} hf hg => ?_
           zero_mem' := ?_
           smul_mem' := fun r {f} hf => ?_ }
  · obtain ⟨F,rfl⟩ := hf
    obtain ⟨G,rfl⟩ := hg
    exact ⟨F.add G,funext (fun x => definableFamilyValue_add P F G x)⟩
  · exact ⟨DefinableRVFamily.constant (gammaEmptyAt (B := B) (n := 0) (Set.subset_univ _)) A,
      funext (fun x => definableFamilyValue_zero P x)⟩
  · obtain ⟨F,rfl⟩ := hf
    let U := (P.rvRepresentative r).2
    refine ⟨(DefinableRVFamily.constant U A).product F,funext (fun x => ?_)⟩
    exact (definableFamilyValue_product P (DefinableRVFamily.constant U A) F x).trans
      (congrArg (fun t => t * P.familyValue F x)
        ((definableFamilyValue_constant P U x).trans (congrArg (P.scalarMap x.val.1) (P.rvRepresentative_class r))))

def IntegrationContext.functionEquiv (P : IntegrationContext B κ hs) (A : Set (Point (M := M) p 0)) :
    P.Function A ≃ P.functionSubmodule A := by
  letI (x : A) := P.coefficientModule x.val.1
  refine Equiv.ofBijective (fun f => ⟨P.functionValue A f,?_⟩) ⟨?_,?_⟩
  · induction f using Quotient.inductionOn with
    | h F => exact ⟨F,rfl⟩
  · intro f g he
    apply definableRVFunction_ext P.countable_le hs P.characteristic P.real_small P.gamma_small P.field_base P.generated
      P.value P.value_mem P.value_large P.section5_two_order A f g
    exact fun x => congrFun (congrArg Subtype.val he) x
  · rintro ⟨f,F,he⟩
    exact ⟨Quotient.mk _ F,Subtype.ext he⟩

@[instance_reducible] def IntegrationContext.functionAddCommMonoid (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) : AddCommMonoid (P.Function A) := by
  letI (x : A) := P.coefficientModule x.val.1
  exact (P.functionEquiv A).addCommMonoid

@[instance_reducible] def IntegrationContext.functionModule (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) :
    letI := P.functionAddCommMonoid A
    Module P.RV (P.Function A) := by
  letI (x : A) := P.coefficientModule x.val.1
  letI := P.functionAddCommMonoid A
  exact (P.functionEquiv A).addEquiv.module P.RV

def IntegrationContext.functionLinearEquiv (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) p 0)) :
    letI (x : A) := P.coefficientModule x.val.1
    letI := P.functionAddCommMonoid A
    letI := P.functionModule A
    P.Function A ≃ₗ[P.RV] P.functionSubmodule A := by
  letI (x : A) := P.coefficientModule x.val.1
  letI := P.functionAddCommMonoid A
  letI := P.functionModule A
  exact (P.functionEquiv A).addEquiv.linearEquiv P.RV

end IntegrationInACVF.Section6.FiniteRV
