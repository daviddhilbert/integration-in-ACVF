import Integration7.LiteralVolumeLiftMaps
import Integration7.VFVolumeParameterExtension
import IntegrationSection6.FiniteRVParameterExtension

/-! A source RV density on its literal VF presentation, retaining the
density label and the exact form through a real parameter extension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S R : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def literalRVVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    (F : @RVFiniteObject M N S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1)
      (@RVObject.arity M N S (k+1) F.obj))
    (h : @Section6.PresentsLift M N hN S (k+1) F.obj (Section6.normalizedPointSet A)) :
    VolumeForm (rawSpecialSet hc A) :=
  (rvVolumeLift (⟨canonicalFiniteRVObject hc F, ω⟩ : PositiveRVVolumeObject (M := M) S k)).form.pullback
    (literalVolumeLiftMap hc _ A (canonicalRVObject_presentsLift hc h))

theorem literalRVVolumeForm_density (hc : CanonicalStructure.IsCanonical (M := M))
    (F : @RVFiniteObject M N S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1)
      (@RVObject.arity M N S (k+1) F.obj))
    (h : @Section6.PresentsLift M N hN S (k+1) F.obj (Section6.normalizedPointSet A))
    (δ : Fin (@RVObject.arity M N S (k+1) F.obj)) (hω : ∀ u, ω.value u = u.val δ)
    (p : rawSpecialSet hc A) : (literalRVVolumeForm hc F ω A h).value p = p.val.2 δ := by
  change ω.value _ = _
  rw [hω]
  rfl

theorem literalRVVolumeForm_extend (hc : CanonicalStructure.IsCanonical (M := M))
    (F : @RVFiniteObject M N S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    (A : SpecialTransformations.Section5.DefSet (M := M) S (k+1)
      (@RVObject.arity M N S (k+1) F.obj))
    (h : @Section6.PresentsLift M N hN S (k+1) F.obj (Section6.normalizedPointSet A))
    (hSR : S ⊆ R) :
    literalRVVolumeForm hc (@Section6.FiniteRV.extendObject M N S R (k+1) hSR F)
      (ω.extend hSR) (SpecialTransformations.Section5.extendBase A hSR)
      (Section6.normalizedPresentsLift_extendBase hSR h) =
        (literalRVVolumeForm hc F ω A h).extend hSR := rfl

end IntegrationInACVF.Section7
