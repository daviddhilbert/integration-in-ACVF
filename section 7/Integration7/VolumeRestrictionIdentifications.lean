import Integration7.VolumeRelabeling

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeRestrictionCarrierIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A B : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hB : B.carrier ⊆ U.underlying.obj.domain.carrier) (hAB : A.carrier = B.carrier) :
    RVVolumeIso (U.restrict A hA) (U.restrict B hB) := by
  let L := U.restrict A hA
  let R := U.restrict B hB
  let F : Map A B := Map.inclusion hAB.le
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun x : B => x.val) he)
    · intro b
      exact ⟨⟨b.val, hAB.ge b.property⟩, rfl⟩
  let e : L.underlying ≅ R.underlying := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection (U := L.underlying.obj) (V := R.underlying.obj) F hF (fun _ => rfl))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e (fun _ => rfl) (fun _ => rfl)

def volumeRestrictionTransIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A B : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) (hBA : B.carrier ⊆ A.carrier) :
    RVVolumeIso ((U.restrict A hA).restrict B hBA) (U.restrict B (hBA.trans hA)) := by
  let L := (U.restrict A hA).restrict B hBA
  let R := U.restrict B (hBA.trans hA)
  let e : L.underlying ≅ R.underlying := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection (U := L.underlying.obj) (V := R.underlying.obj)
      (Map.id B) Function.bijective_id (fun _ => rfl))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e (fun _ => rfl) (fun _ => rfl)

end IntegrationInACVF.Section7
