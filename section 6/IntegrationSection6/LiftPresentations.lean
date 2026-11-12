import Section5.PullbackLift

/-! The raw canonical lift in the predecessor's actual special-bijection space. -/

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

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

/-- The reverse of the inherited raw-point presentation map, on the same
actual VF/RV tuples. No new language, representatives or parameters are added. -/
def fromRawPointMap (A : PresentedSet (rawPointSpace (M := M) n m) S) :
    Map A (PresentedSet.univ (pointSpace n m) S) := by
  have hd (c : pDomain (rawPointSpace (M := M) n m)) : c.val ∈ pDomain (pointSpace n m) := by
    constructor
    · intro i
      have he := congrFun (rawVF_decode_values
        (⟨c.val ∘ Sum.inl, c.property.1⟩ : pDomain (rawVFSpace n))) i
      change (pDecode (rawVFSpace n) ⟨c.val ∘ Sum.inl,c.property.1⟩ i).val = c.val (.inl i) at he
      change iVF (c.val (.inl i))
      rw [← he]
      exact (pDecode (rawVFSpace n) ⟨c.val ∘ Sum.inl, c.property.1⟩ i).property
    · intro i
      have he := congrFun (rawRV_decode_values
        (⟨c.val ∘ Sum.inr, c.property.2⟩ : pDomain (rawRVSpace m))) i
      change (pDecode (rawRVSpace m) ⟨c.val ∘ Sum.inr,c.property.2⟩ i).val = c.val (.inr i) at he
      change iRV (c.val (.inr i))
      rw [← he]
      exact (pDecode (rawRVSpace m) ⟨c.val ∘ Sum.inr, c.property.2⟩ i).property
  refine Map.ofCodes A (fun p => p) (fun z => z) (fun i => rawProj S i) hd ?_
  intro c
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact (congrFun (rawVF_decode_values
      (⟨c.val ∘ Sum.inl, c.property.1⟩ : pDomain (rawVFSpace n))) i).symm
  · funext i
    apply Subtype.ext
    exact (congrFun (rawRV_decode_values
      (⟨c.val ∘ Sum.inr, c.property.2⟩ : pDomain (rawRVSpace m))) i).symm

local notation "N" => (@CanonicalStructure.normalize M sM)

/-- The inherited canonical lift, represented in the actual focus/chain space. -/
def typedLift (U : @SpecialTransformations.Section4.RVObject M N S n) :
    DefSet (M := M) S n (rvObjectArity U) := Map.image (fromRawPointMap (rawLift U))

theorem typedLift_mem (U : @SpecialTransformations.Section4.RVObject M N S n)
    (p : Point (M := M) n (rvObjectArity U)) :
    p ∈ carrier (typedLift U) ↔ p ∈ carrier (rawLift U) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ha ▸ a.property
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

def typedLiftRawMap (U : @SpecialTransformations.Section4.RVObject M N S n) :
    Map (typedLift U) (rawLift U) :=
  Map.corestrict (rawPointMap (typedLift U)) (fun a => (typedLift_mem U a.val).mp a.property)

theorem typedLiftRawMap_bijective (U : @SpecialTransformations.Section4.RVObject M N S n) :
    Function.Bijective (typedLiftRawMap U) := by
  constructor
  · intro a b he
    apply Subtype.ext
    change a.val = b.val
    have he' := congrArg (fun x : rawLift U => x.val) he
    simpa only [typedLiftRawMap, Map.corestrict, rawPointMap,
      SpecialTransformations.DefinableGeometry.Map.ofCodes_apply] using he'
  · intro q
    exact ⟨⟨q.val, (typedLift_mem U q.val).mpr q.property⟩, Subtype.ext rfl⟩

/-- A canonical lift is an RV-pullback in the inherited geometric sense. -/
theorem typedLift_pullback (U : @SpecialTransformations.Section4.RVObject M N S n) :
    IsRVPullback (carrier (typedLift U)) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q hpq
  obtain ⟨u, hu, hv⟩ := (typedLift_mem U p).mp hp
  obtain ⟨hfield, hlabels⟩ := (sameRV_iff p q).mp hpq
  apply (typedLift_mem U q).mpr
  refine ⟨u, hu.trans hlabels, ?_⟩
  exact hv.trans ((@normalized_tupleRV M sM hM n p.1).trans
    ((funext hfield).trans (@normalized_tupleRV M sM hM n q.1).symm))

end IntegrationInACVF.Section6
