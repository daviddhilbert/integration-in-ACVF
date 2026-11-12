import IntegrationSection6.ProjectionFamilyInputs
import IntegrationSection6.RelativeFamilyRepresentations
import IntegrationSection6.VFParameterRowIntegrals
import IntegrationSection6.ContextDefinableFunctions

/-! Coordinate fibre integration has a definable RV-family representative,
and integrating that representative equals the original total integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {n p : ℕ}

def projectionFamilyRepresentation (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A) :
    RelativeFamilyRepresentation B (E.baseImage A) (projectionFamilyDomain E A F.schema) :=
  Classical.choice (relativeFamilyRepresentation_exists P.countable_le hs P.characteristic P.real_small P.field_base
    (E.baseImage A) (projectionFamilyDomain E A F.schema) (projectionFamily_definable E A hA F.schema)
    (projectionFamily_finite E A hA F.schema F.finite) (projectionFamily_base E A F.schema))

def projectionRepresentative (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A) :
    DefinableRVFamily B (E.baseImage A) where
  arity := (projectionFamilyRepresentation P E A hA F).arity
  degree := E.discarded + F.degree
  schema := (projectionFamilyRepresentation P E A hA F).schema
  finite := (projectionFamilyRepresentation P E A hA F).finite

def projectionFibreIntegral (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A)
    (x : E.baseImage A) : (P.atVF x.val.1).RV :=
  P.rowIntegral (projectionFamilyDomain E A F.schema) (projectionFamily_definable E A hA F.schema)
    (projectionFamily_finite E A hA F.schema F.finite) x.val.1

theorem projectionRepresentative_value (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A)
    (x : E.baseImage A) :
    P.familyValue (projectionRepresentative P E A hA F) x = projectionFibreIntegral P E A hA F x := by
  let R := projectionFamilyRepresentation P E A hA F
  have he := P.rowIntegral_iso (projectionFamilyDomain E A F.schema) (familyLiftDomain (E.baseImage A) R.schema)
    (projectionFamily_definable E A hA F.schema) (gamma_family_lift_definable _ (E.gamma_baseImage A hA) R.schema)
    (projectionFamily_finite E A hA F.schema F.finite)
    (gammaFamilyLift _ (E.gamma_baseImage A hA) R.schema R.finite).finiteFibres R.iso R.parameters x.val.1
  exact (he.trans (P.rowIntegral_familyLift _ (E.gamma_baseImage A hA) R.schema R.finite x)).symm

theorem projectionRepresentative_integral (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A) :
    P.integral (E.baseImage A) (E.gamma_baseImage A hA) (Quotient.mk _ (projectionRepresentative P E A hA F)) =
      P.integral A hA (Quotient.mk _ F) := by
  let R := projectionFamilyRepresentation P E A hA F
  let e := (projectionFamilyIso E A hA F.schema).trans (gammaLogicInput B) R.iso
  exact congrArg (globalAdditiveIntegrationToSemiring P.countable_le hs P.characteristic P.real_small P.field_base
      P.gamma_small P.value P.value_mem P.value_large P.section5_two_order P.generated)
    (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) ⟨e.symm (gammaLogicInput B)⟩)

end IntegrationInACVF.Section6
