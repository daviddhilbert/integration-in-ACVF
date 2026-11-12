import IntegrationSection6.NormalizedPresentations
import IntegrationSection6.LiftCarrierGeometry

/-! The actual canonical lift has the literal lift-carrier presentation
required by the full-focus blowup theorem, in the normalized ambient model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

/-- No definable bijection or image computation is assumed: this follows
from the inherited canonical lift's literal carrier. -/
theorem normalizedTypedLift_presents
    (U : @SpecialTransformations.Section4.RVObject M
      (@CanonicalStructure.normalize M sM) S n) :
    @PresentsLift M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) S n U
      (normalizedPointSet (typedLift U)) := by
  intro p
  exact typedLift_mem U p

end IntegrationInACVF.Section6
