import IntegrationSection6.LiftPresentations

/-! The canonical image of an RV-pullback is literally its actual lift
presentation, with identity on every VF and RV coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def canonicalImageLiftMap (A : DefSet (M := M) S n m) :
    Map (canonicalImage A) (rawLift (pullbackObject A)) :=
  Map.corestrict (rawPointMap (canonicalImage A)) (by
    intro p
    obtain ⟨a,ha⟩ := p.property
    have h := canonicalRawMap_mem_lift A a
    have he : (canonicalRawMap A a).val = p.val := ha
    change p.val ∈ carrier (rawLift (pullbackObject A))
    exact he ▸ h)

@[simp] theorem canonicalImageLiftMap_value (A : DefSet (M := M) S n m)
    (a : canonicalImage A) : (canonicalImageLiftMap A a).val = a.val := rfl

@[simp] theorem canonicalImageLiftMap_square (A : DefSet (M := M) S n m) (a : A) :
    canonicalImageLiftMap A (Map.toImage (canonicalMap A) a) = pullbackLiftMap A a := rfl

theorem canonicalImageLiftMap_bijective (A : DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) : Function.Bijective (canonicalImageLiftMap A) := by
  constructor
  · intro a b he
    exact Subtype.ext (congrArg (fun q : rawLift (pullbackObject A) => q.val) he)
  · intro b
    obtain ⟨a,ha⟩ := (pullbackLiftMap_bijective A hA).2 b
    exact ⟨Map.toImage (canonicalMap A) a,ha⟩

end IntegrationInACVF.Section6
