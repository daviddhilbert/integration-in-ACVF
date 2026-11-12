import IntegrationSection6.CanonicalRVKeys
import IntegrationSection6.ElementaryIsomorphism
import IntegrationSection6.Subobjects
import IntegrationSection6.VolumePreservingLift

/-! Transport of elementary constructions along a volume-preserving RV
bijection uses no smallness or saturation hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ} {U V : RVObject (M := M) S n}

theorem elementaryMap_preserves_volume (F : Map U.domain V.domain) (i : Fin n)
    (hvol : ∀ u, V.value (F u) = U.value u) (a : (elementary U i).domain) :
    (elementary V i).value (elementaryMap i i F a) = (elementary U i).value a := by
  rw [elementary_value,elementaryMap_projection,elementaryMap_parameter,hvol,elementary_value]

def elementaryVolumePreservingIso (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hvol : ∀ u, V.value (F u) = U.value u) (i : Fin n) :
    elementary U i ≅ elementary V i :=
  rvIsoOfVolumePreservingBijection (elementaryMap i i F)
    (elementaryMap_bijective i i F hF) (elementaryMap_preserves_volume F i hvol)

theorem canonicalRVKeyIso_inv_volume (U : RVObject (M := M) S n)
    (a : (canonicalRVKeyObject U).domain) :
    U.value ((canonicalRVKeyIso U).inv.map a) = (canonicalRVKeyObject U).value a := by
  have he := canonicalRVKeyIso_volume U ((canonicalRVKeyIso U).inv.map a)
  rw [iso_inv_hom_apply] at he
  exact he.symm

/-- Drop the preparatory canonical labels after making the elementary
construction. The new blowup parameter is retained. -/
def canonicalElementaryIso (U : RVObject (M := M) S n) (i : Fin n) :
    elementary (canonicalRVKeyObject U) i ≅ elementary U i :=
  elementaryVolumePreservingIso (canonicalRVKeyIso U).inv.map
    (iso_map_bijective (canonicalRVKeyIso U).symm) (canonicalRVKeyIso_inv_volume U) i

theorem canonicalElementaryIso_volume (U : RVObject (M := M) S n) (i : Fin n)
    (a : (elementary (canonicalRVKeyObject U) i).domain) :
    (elementary U i).value ((canonicalElementaryIso U i).hom.map a) =
      (elementary (canonicalRVKeyObject U) i).value a :=
  elementaryMap_preserves_volume (canonicalRVKeyIso U).inv.map i (canonicalRVKeyIso_inv_volume U) a

def canonicalElementaryLift (U : RVObject (M := M) S n) (i : Fin n) :=
  volumePreservingLiftMap (canonicalElementaryIso U i).hom.map (canonicalElementaryIso_volume U i)

theorem canonicalElementaryLift_bijective (U : RVObject (M := M) S n) (i : Fin n) :
    Function.Bijective (canonicalElementaryLift U i) :=
  volumePreservingLiftMap_bijective _ _ (iso_map_bijective (canonicalElementaryIso U i))

@[simp] theorem canonicalElementaryLift_vf (U : RVObject (M := M) S n) (i : Fin n)
    (a : rvLift (elementary (canonicalRVKeyObject U) i)) :
    (canonicalElementaryLift U i a).val.1 = a.val.1 := rfl

end IntegrationInACVF.Section6
