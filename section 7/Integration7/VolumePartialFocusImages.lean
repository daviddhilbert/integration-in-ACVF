import Integration7.VolumeFocusActiveLoci
import Integration7.PullbackCoordinateVolumeObjects
import Integration7.RetainedVolumeLabels
import IntegrationSection6.PartialFocusBlowup
import IntegrationSection6.FiniteBlowups

/-! The full image of a partial focus has finite RV volume and the
same retained density label. Both assertions come from the actual step. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Focus carrier pullbackObject rvObjectVolume)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : @RVFiniteObject M N (C.base : Set M) (k+1))
variable (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
  (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
variable (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
variable {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)

theorem partialFocusImage_finite
    (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)
 :
    @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _ (rvObjectVolume (Section6.originalFocusObject D)) := by
  let b := Section6.partialFocusBlowup h D C.uncountable.le C.saturated C.small
  exact @Section6.Blowup.finite_volume M N hN (C.base : Set M) (k+1) F.obj
    (Section6.originalFocusObject D) C.κ C.uncountable.le
    (@Saturated.normalize M sM C.κ C.saturated) C.small b F.property

def partialFocusVolumeImage
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)

    (δ : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj))
    (hDensity : ∀ u, ω.value u = u.val δ) : PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  pullbackCoordinateVolumeObject hc D.etaImage (partialFocusImage_finite C F h D) δ
    (focus_density_label_nonzero D δ (lift_density_label_nonzero
      (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalRVObject_presentsLift hc h) δ hDensity))

theorem partialFocusVolumeImage_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)

    (δ : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj))
    (hDensity : ∀ u, ω.value u = u.val δ)
    (u : (partialFocusVolumeImage hc C F ω h D δ hDensity).underlying.obj.domain) :
    (partialFocusVolumeImage hc C F ω h D δ hDensity).form.value u = u.val (Fin.natAdd (k+1) δ) := rfl

end IntegrationInACVF.Section7
