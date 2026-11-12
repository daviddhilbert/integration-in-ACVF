import IntegrationSection6.CanonicalImageLift
import IntegrationSection6.NormalizedLifts

/-! Canonicalization of any actual RV-pullback is its literal lift
presentation, with its original canonical RV image object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem canonicalImage_carrier_eq_typedLift (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) :
    carrier (canonicalImage A) = carrier (typedLift (pullbackObject A)) := by
  ext p
  rw [typedLift_mem]
  constructor
  · intro hp
    exact (canonicalImageLiftMap A ⟨p,hp⟩).property
  · intro hp
    obtain ⟨a,ha⟩ := (canonicalImageLiftMap_bijective A hA).2 ⟨p,hp⟩
    have he : a.val = p := congrArg (fun b : rawLift (pullbackObject A) => b.val) ha
    exact he ▸ a.property

theorem normalizedCanonicalImage_presents (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) :
    @PresentsLift M N hN S n (pullbackObject A) (normalizedPointSet (canonicalImage A)) := by
  have he := canonicalImage_carrier_eq_typedLift A hA
  have hp := normalizedTypedLift_presents (pullbackObject A)
  intro p
  exact (Set.ext_iff.mp he p).trans (hp p)

end IntegrationInACVF.Section6
