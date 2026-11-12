import IntegrationSection6.ParameterExtension
import IntegrationSection6.NormalizedPresentations
import IntegrationSection6.LiftCarrierGeometry
import IntegrationSection6.FiniteRVGeometry
import Section5.ParameterExtension

/-! Extending an internal real presentation retains the actual RV[k]
object and literal lift carrier. This introduces no new original-Gamma names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalizedPresentsLift_extendBase (hSR : S ⊆ R)
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) :
    @PresentsLift M N hN R n (@extendObject M N S R n hSR U)
      (normalizedPointSet (extendBase A hSR)) := by
  intro p
  exact h p

namespace FiniteRV
variable {M : Type} [LRV.Structure M]

def extendObject {S R : Set M} {n : ℕ} (hSR : S ⊆ R) (U : RVFiniteObject (M := M) S n) :
    RVFiniteObject (M := M) R n :=
  ⟨IntegrationInACVF.Section6.extendObject hSR U.obj,U.property⟩

end FiniteRV
end IntegrationInACVF.Section6
