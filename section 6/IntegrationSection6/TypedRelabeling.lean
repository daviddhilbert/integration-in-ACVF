import IntegrationSection6.CanonicalImageLift
import IntegrationSection6.VolumePreservingLift

/-! Lift relabelings in the actual special-bijection presentation. -/
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
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def rawLiftToTypedMap (U : @RVObject M N S n) : Map (rawLift U) (typedLift U) :=
  Map.corestrict (fromRawPointMap (rawLift U)) (fun a => (typedLift_mem U a.val).mpr a.property)

theorem rawLiftToTypedMap_bijective (U : @RVObject M N S n) :
    Function.Bijective (rawLiftToTypedMap U) := by
  constructor
  · intro a b he
    exact Subtype.ext (congrArg (fun p : typedLift U => p.val) he)
  · intro a
    exact ⟨typedLiftRawMap U a,Subtype.ext rfl⟩

def canonicalImageRelabelMap (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (V : @RVObject M N S n)
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S
      (@rvObjectDomain M sM S n (pullbackObject A)) (@rvObjectDomain M sM S n V))
    (hvol : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ a, V.value (F a) = (@pullbackObject M sM hM S n m A).value a) :
    Map (canonicalImage A) (typedLift V) :=
  Map.comp (rawLiftToTypedMap V)
    (Map.comp (@volumePreservingLiftMap M N hN S n (pullbackObject A) V F hvol)
      (canonicalImageLiftMap A))

theorem canonicalImageRelabelMap_bijective (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (hA : IsRVPullback (carrier A)) (V : @RVObject M N S n)
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S
      (@rvObjectDomain M sM S n (pullbackObject A)) (@rvObjectDomain M sM S n V))
    (hvol : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ a, V.value (F a) = (@pullbackObject M sM hM S n m A).value a)
    (hF : Function.Bijective F) : Function.Bijective (canonicalImageRelabelMap A V F hvol) :=
  (rawLiftToTypedMap_bijective V).comp
    ((@volumePreservingLiftMap_bijective M N hN S n (pullbackObject A) V F hvol hF).comp
      (canonicalImageLiftMap_bijective A hA))

@[simp] theorem canonicalImageRelabelMap_value (A : SpecialTransformations.Section5.DefSet (M := M) S n m)
    (V : @RVObject M N S n)
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S
      (@rvObjectDomain M sM S n (pullbackObject A)) (@rvObjectDomain M sM S n V))
    (hvol : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ a, V.value (F a) = (@pullbackObject M sM hM S n m A).value a)
    (a : canonicalImage A) :
    (canonicalImageRelabelMap A V F hvol a).val =
      (a.val.1,(F (@liftLabelProjection M N hN S n (pullbackObject A) (canonicalImageLiftMap A a))).val) := rfl

end IntegrationInACVF.Section6
