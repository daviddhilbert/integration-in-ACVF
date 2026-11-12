import IntegrationSection6.LiftLoci
import IntegrationSection6.CanonicalRVKeys
import IntegrationSection6.KeyInverseCoordinates

/-! Canonical RV data of an actual literal lift recovers its input RV
object, up to the explicit volume-preserving canonical label isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem normalizedPresentsLift_key_domains {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) :
    carrier (rvObjectDomain (pullbackObject A)) =
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S
        (@RVObject.domain M N S n (@canonicalRVKeyObject M N S n U)) := by
  have hk (a : A) (u : rvObjectDomain U) (hu : u.val = a.val.2)
      (hv : @RVObject.value M N S n U u = fun j => @rv M N hN (a.val.1 j)) :
      (rawKeyMap A a).val = (@canonicalRVKeyMap M N S n U u).val := by
    rw [rawKeyMap_apply]
    change Fin.append (fun j => rv (a.val.1 j)) a.val.2 =
      Fin.append (@RVObject.value M N S n U u) u.val
    rw [hu,hv]
    apply congrArg (fun t => Fin.append t a.val.2)
    funext j
    exact (rv_normalize _).symm
  ext r
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨u,hu,hv⟩ := (h a.val).mp a.property
    exact ⟨u,(hk a u hu hv).symm.trans ha⟩
  · rintro ⟨u,hu⟩
    obtain ⟨p,hp,hv⟩ := @PresentsLift.representative M N hN S n U (normalizedPointSet A) h u
    let a : A := ⟨p.val,p.property⟩
    exact ⟨a,(hk a u hp.symm hv.symm).trans hu⟩

def pullbackPresentationIso {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@pullbackObject M sM hM S n (@rvObjectArity M sM S n U) A) ≅ U := by
  let R := pullbackObject A
  have he := normalizedPresentsLift_key_domains h
  letI := N
  letI := hN
  exact (rvIsoOfCarrierEq R.domain (canonicalRVKeyObject U).domain R.volume
    (canonicalRVKeyObject U).volume he (fun _ => rfl)).trans (canonicalRVKeyIso U).symm

end IntegrationInACVF.Section6
