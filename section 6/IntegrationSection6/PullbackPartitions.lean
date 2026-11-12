import IntegrationSection6.Subobjects
import IntegrationSection6.LiftPresentations
import Section4.RVAppend

/-! Canonical RV data preserves a disjoint partition into RV-pullbacks.
The comparison is an actual volume-preserving definable RV isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section5.pullbackObject
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {A C E : SpecialTransformations.Section5.DefSet (M := M) S n m}

theorem pullbackObject_domain_mono (hCA : carrier C ⊆ carrier A) :
    carrier (rvObjectDomain (pullbackObject C)) ⊆ carrier (rvObjectDomain (pullbackObject A)) := by
  rintro r ⟨c,hc⟩
  exact ⟨⟨c.val,hCA c.property⟩,hc⟩

theorem pullbackObject_domains_union (hA : carrier A = carrier C ∪ carrier E) :
    carrier (rvObjectDomain (pullbackObject A)) =
      carrier (rvObjectDomain (pullbackObject C)) ∪ carrier (rvObjectDomain (pullbackObject E)) := by
  ext r
  constructor
  · rintro ⟨a,ha⟩
    have hp := (Set.ext_iff.mp hA a.val).mp a.property
    rcases hp with hp | hp
    · exact Or.inl ⟨⟨a.val,hp⟩,ha⟩
    · exact Or.inr ⟨⟨a.val,hp⟩,ha⟩
  · rintro (⟨a,ha⟩ | ⟨a,ha⟩)
    · exact ⟨⟨a.val,(Set.ext_iff.mp hA a.val).mpr (Or.inl a.property)⟩,ha⟩
    · exact ⟨⟨a.val,(Set.ext_iff.mp hA a.val).mpr (Or.inr a.property)⟩,ha⟩

theorem pullbackObject_domains_disjoint (hCE : Disjoint (carrier C) (carrier E))
    (hC : IsRVPullback (carrier C)) :
    Disjoint (carrier (rvObjectDomain (pullbackObject C)))
      (carrier (rvObjectDomain (pullbackObject E))) := by
  apply Set.disjoint_left.mpr
  rintro r ⟨c,hc⟩ ⟨e,he⟩
  have hkey := (rawKeyMap_apply C c).symm.trans (hc.trans (he.symm.trans (rawKeyMap_apply E e)))
  have hs : SameRV c.val e.val := by
    apply (sameRV_iff _ _).mpr
    constructor
    · intro j
      simpa only [Fin.append_left,vfAt] using congrFun hkey (Fin.castAdd m j)
    · funext j
      simpa only [Fin.append_right] using congrFun hkey (Fin.natAdd n j)
  exact Set.disjoint_left.mp hCE ((isRVPullback_iff _).mp hC c.val c.property e.val hs) e.property

def pullbackPartitionIso (hA : carrier A = carrier C ∪ carrier E)
    (hCE : Disjoint (carrier C) (carrier E)) (hC : IsRVPullback (carrier C)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@pullbackObject M sM hM S n m A) ≅
      rvCoprodObject (@pullbackObject M sM hM S n m C) (@pullbackObject M sM hM S n m E) := by
  let U := pullbackObject A
  let V := pullbackObject C
  let W := pullbackObject E
  have hc := pullbackObject_domain_mono (show carrier C ⊆ carrier A from fun _ h => hA ▸ Or.inl h)
  have hu := pullbackObject_domains_union hA
  have hd := pullbackObject_domains_disjoint hCE hC
  letI := N
  letI := hN
  have he : (complement U V.domain).carrier = W.domain.carrier := by
    ext r
    constructor
    · rintro ⟨hr,hn⟩
      rcases (Set.ext_iff.mp hu r).mp hr with h | h
      · exact False.elim (hn h)
      · exact h
    · intro hr
      exact ⟨(Set.ext_iff.mp hu r).mpr (Or.inr hr),fun h => Set.disjoint_left.mp hd h hr⟩
  let eC := rvIsoOfCarrierEq (U.restrict V.domain hc).domain V.domain
    (U.restrict V.domain hc).volume V.volume rfl (fun _ => rfl)
  let eE := rvIsoOfCarrierEq (U.restrict (complement U V.domain) (complement_subset U V.domain)).domain W.domain
    (U.restrict (complement U V.domain) (complement_subset U V.domain)).volume W.volume he (fun _ => rfl)
  exact (partitionIso U V.domain hc).symm.trans (rvCoprodIso eC eE)

end IntegrationInACVF.Section6
