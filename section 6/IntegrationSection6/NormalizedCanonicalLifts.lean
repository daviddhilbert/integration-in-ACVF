import IntegrationSection6.CanonicalLiftKeys
import IntegrationSection6.NormalizedLifts

/-! The canonical tagged lift has exactly the canonically labeled RV
object, in the same released normalized presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalizedPresentsLift_canonical {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) :
    @PresentsLift M N hN S n (@canonicalRVKeyObject M N S n U)
      (@normalizedPointSet M sM hM S n (n+rvObjectArity U) (canonicalImage A)) := by
  have hc := @PresentsLift.canonical M N hN S n U (normalizedPointSet A) h
  rw [@canonicalImage_normalize M sM hM S n (rvObjectArity U) A] at hc
  exact hc

def canonicalTypedLift (U : @RVObject M N S n) := canonicalImage (typedLift U)

theorem normalizedCanonicalTypedLift_presents (U : @RVObject M N S n) :
    @PresentsLift M N hN S n (@canonicalRVKeyObject M N S n U)
      (@normalizedPointSet M sM hM S n (n+rvObjectArity U) (canonicalTypedLift U)) :=
  normalizedPresentsLift_canonical (@normalizedTypedLift_presents M sM hM S n U)

theorem canonicalTypedLift_tagged (U : @RVObject M N S n) (i : Fin n) :
    Tagged (carrier (canonicalTypedLift U)) i (Fin.castAdd (rvObjectArity U) i) :=
  canonicalLiftKeys_tagged (typedLift U) i

end IntegrationInACVF.Section6
