import Integration7.CanonicalVolumePresentations
import Integration7.FiniteVolumeIsoMaps
import IntegrationSection6.FiniteBlowups

/-! Transport actual finite RV objects and their isomorphisms from the
released normalized presentation to the canonical original structure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def canonicalRVObject (hc : CanonicalStructure.IsCanonical (M := M)) (U : @RVObject M N S n) :
    RVObject (M := M) S n where
  arity := @RVObject.arity M N S n U
  domain := canonicalRawRVDomain hc (@RVObject.domain M N S n U)
  volume := (canonicalRawRVMap hc (@RVObject.volume M N S n U)).toUniv

def canonicalFiniteRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : @RVFiniteObject M N S n) : RVFiniteObject (M := M) S n :=
  ⟨canonicalRVObject hc U.obj,fun t => U.property ⟨t.val,Set.mem_univ _⟩⟩

def canonicalRVHom (hc : CanonicalStructure.IsCanonical (M := M)) {U V : @RVObject M N S n}
    (f : @RVHom M N S n U V) : RVHom (canonicalRVObject hc U) (canonicalRVObject hc V) where
  map := canonicalRawRVMap hc (@RVHom.map M N S n U V f)
  volumetric := @RVHom.volumetric M N S n U V f
  finite_volume_images := @RVHom.finite_volume_images M N S n U V f

def canonicalRVIso (hc : CanonicalStructure.IsCanonical (M := M)) {U V : @RVObject M N S n}
    (e : U ≅ V) : canonicalRVObject hc U ≅ canonicalRVObject hc V where
  hom := canonicalRVHom hc e.hom
  inv := canonicalRVHom hc e.inv
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro u
    exact Subtype.ext (congrArg Subtype.val (@Section6.iso_hom_inv_apply M N hN S n U V e ⟨u.val,u.property⟩))
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro v
    exact Subtype.ext (congrArg Subtype.val (@Section6.iso_inv_hom_apply M N hN S n U V e ⟨v.val,v.property⟩))

def canonicalFiniteRVIso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : @RVFiniteObject M N S n} (e : U ≅ V) : canonicalFiniteRVObject hc U ≅ canonicalFiniteRVObject hc V :=
  rvFiniteIsoOfAmbient (canonicalRVIso hc ((@finiteVolumeProperty M N S n).ι.mapIso e))

end IntegrationInACVF.Section7
