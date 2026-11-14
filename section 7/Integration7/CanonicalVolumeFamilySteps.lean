import Integration7.CanonicalVolumeLabels
import Integration7.CanonicalFiniteRVObjects
import IntegrationSection6.NormalizedCanonicalLifts

/-! Canonical labeling in a literal lift family is a volume
isomorphism, in the released normalized presentation used by chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def canonicalFiniteRVKeys (F : @RVFiniteObject M N S (k+1)) : @RVFiniteObject M N S (k+1) :=
  ⟨@Section6.canonicalRVKeyObject M N S (k+1) F.obj,
    (@Section6.finite_volume_iso M N hN S (k+1) F.obj _
      (@Section6.canonicalRVKeyIso M N hN S (k+1) F.obj)).mp F.property⟩

def canonicalFiniteVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    (F : @RVFiniteObject M N S (k+1)) (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain) :
    VolumeForm (canonicalFiniteRVObject hc (canonicalFiniteRVKeys F)).obj.domain :=
  (canonicalVolumeLabels (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) S k)).form

def canonicalVolumeFamilyIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain) :
    RVVolumeIso (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      ⟨canonicalFiniteRVObject hc (canonicalFiniteRVKeys F),canonicalFiniteVolumeForm hc F ω⟩ :=
  canonicalVolumeLabelsIso hc C ⟨canonicalFiniteRVObject hc F,ω⟩

theorem canonicalFiniteVolumeForm_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : @RVFiniteObject M N S (k+1)) (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (δ : Fin (@RVObject.arity M N S (k+1) F.obj)) (hDensity : ∀ u, ω.value u = u.val δ)
    (u : (canonicalFiniteRVObject hc (canonicalFiniteRVKeys F)).obj.domain) :
    (canonicalFiniteVolumeForm hc F ω).value u = u.val (Fin.natAdd (k+1) δ) :=
  canonicalVolumeLabels_density_label
    (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) S k) δ hDensity u

end IntegrationInACVF.Section7
