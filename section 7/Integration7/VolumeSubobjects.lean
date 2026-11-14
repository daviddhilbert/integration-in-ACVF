import Integration7.VolumeIsomorphismRestriction
import IntegrationSection6.Subobjects

/-! The actual image of an essential definable source subobject under a
volume isomorphism, over the unchanged parameter base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U V : PositiveRVVolumeObject (M := M) S k}

def volumeSubobjectImage (f : RVVolumeIso U V)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier) :
    DefSet (rawRVSpace (M := M) V.underlying.obj.arity) S := by
  let E : U.essential.obj ≅ V.essential.obj := (finiteVolumeProperty S (k + 1)).ι.mapIso f.iso
  exact Section6.subobjectImage (U := U.essential.obj) (V := V.essential.obj) E A hA

theorem volumeSubobjectImage_subset (f : RVVolumeIso U V)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier) :
    (volumeSubobjectImage f A hA).carrier ⊆ V.essential.obj.domain.carrier := by
  let E : U.essential.obj ≅ V.essential.obj := (finiteVolumeProperty S (k + 1)).ι.mapIso f.iso
  exact Section6.subobjectImage_subset (U := U.essential.obj) (V := V.essential.obj) E A hA

def volumeSubobjectUnderlyingIso (f : RVVolumeIso U V)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier) :
    (U.restrict A (hA.trans (rvEssentialLabels_subset U.underlying.obj))).underlying ≅
      (V.restrict (volumeSubobjectImage f A hA)
        ((volumeSubobjectImage_subset f A hA).trans (rvEssentialLabels_subset V.underlying.obj))).underlying := by
  let E : U.essential.obj ≅ V.essential.obj := (finiteVolumeProperty S (k + 1)).ι.mapIso f.iso
  let e := Section6.subobjectImageIso (U := U.essential.obj) (V := V.essential.obj) E A hA
  exact rvFiniteIsoOfAmbient e

def RVVolumeIso.subobjectImage
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (f : RVVolumeIso U V)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier) :
    RVVolumeIso (U.restrict A (hA.trans (rvEssentialLabels_subset U.underlying.obj)))
      (V.restrict (volumeSubobjectImage f A hA)
        ((volumeSubobjectImage_subset f A hA).trans (rvEssentialLabels_subset V.underlying.obj))) := by
  let L := U.restrict A (hA.trans (rvEssentialLabels_subset U.underlying.obj))
  let R := V.restrict (volumeSubobjectImage f A hA)
    ((volumeSubobjectImage_subset f A hA).trans (rvEssentialLabels_subset V.underlying.obj))
  let i : Map L.essential.obj.domain U.essential.obj.domain :=
    Map.inclusion ((rvEssentialLabels_subset L.underlying.obj).trans hA)
  have hi : Function.Injective i := by
    intro a b h
    exact Subtype.ext (congrArg (fun u : U.essential.obj.domain => u.val) h)
  apply RVVolumeIso.of_injective_restriction hc C f
    (rvFiniteEssentialIso (volumeSubobjectUnderlyingIso f A hA)) i hi
  · intro u
    rfl
  · intro u
    rfl
  · intro u
    rfl
  · intro u
    rfl

end IntegrationInACVF.Section7
