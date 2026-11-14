import Integration7.VolumeFocusPresentations
import Integration7.CanonicalLiftVolumePresentations
import Integration7.EssentialVolumeRestriction
import IntegrationSection6.PartialFocusAdmissibility

/-! The active part of an arbitrary focus is an admissible actual
volume subobject. No admissibility of its inactive part is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Focus carrier)
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

def focusActiveVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)
 : PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k).restrict
    (canonicalRawRVDomain hc (Section6.liftLabelLocus (Section6.focusActiveSet D)))
    (Section6.liftLabelLocus_subset h (Section6.focusActiveSet_subset D))

theorem focusActiveVolumeObject_presents
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)
 :
    Section6.PresentsLift (focusActiveVolumeObject hc C F ω h D).underlying.obj (Section6.focusActiveSet D) :=
  canonicalRVObject_presentsLift hc (Section6.focusActiveRVObject_presents h D)

theorem focusActiveVolumeObject_admissible
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)
 : BlowupAdmissible (focusActiveVolumeObject hc C F ω h D) := by
  have hA := canonicalRVObject_admissible hc (Fin.last k)
    (Section6.focusActiveRVObject_admissible h D C.uncountable.le C.saturated C.small)
  exact ⟨hA.rv_nonzero,hA.algebraic⟩

def focusActiveVolumeBlowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1)
      (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (@RVObject.arity M N (C.base : Set M) (k+1) F.obj)} (D : Focus A (Fin.last k) j)
 :=
  fullFocusPresentedVolumeBlowup hc C (focusActiveVolumeObject hc C F ω h D)
    (focusActiveVolumeObject_presents hc C F ω h D) (Section6.activeFocus D)
    (Section6.activeFocus_full D) (focusActiveVolumeObject_admissible hc C F ω h D)

end IntegrationInACVF.Section7
