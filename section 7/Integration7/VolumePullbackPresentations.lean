import Integration7.PullbackCoordinateVolumeObjects
import Integration7.RetainedVolumeLabels
import IntegrationSection6.PresentationCoordinates

/-! A literal lift recovers its original actual volume object from
canonical RV keys. Both the full volume tuple and density are preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (pullbackObject rvObjectArity rvObjectDomain)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem pullbackPresentation_volume
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @Section6.PresentsLift M N hN S n U (Section6.normalizedPointSet A))
    (a : rvObjectDomain (pullbackObject A)) :
    @RVObject.value M N S n U
      (@RVHom.map M N S n (pullbackObject A) U (Section6.pullbackPresentationIso h).hom a) =
      @RVObject.value M N S n (pullbackObject A) a := by
  let c : @RVObject.domain M N S n (@Section6.canonicalRVKeyObject M N S n U) :=
    ⟨a.val,(Section6.normalizedPresentsLift_key_domains h).le a.property⟩
  have hv := @Section6.canonicalRVKeyIso_volume M N hN S n U
    (@RVHom.map M N S n (@Section6.canonicalRVKeyObject M N S n U) U
      (@Section6.canonicalRVKeyIso M N hN S n U).inv c)
  rw [@Section6.iso_inv_hom_apply M N hN S n U (@Section6.canonicalRVKeyObject M N S n U)] at hv
  exact hv.symm

def presentedPullbackVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    (δ : Fin (rvObjectArity F.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  pullbackCoordinateVolumeObject hc A
    ((@Section6.finite_volume_iso M N hN (C.base : Set M) (k+1) (pullbackObject A) F.obj
      (Section6.pullbackPresentationIso h)).mpr F.property) δ
    (lift_density_label_nonzero
      (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (canonicalRVObject_presentsLift hc h) δ hDensity)

def pullbackVolumePresentationIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    (δ : Fin (rvObjectArity F.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    RVVolumeIso (presentedPullbackVolumeObject hc C F ω h δ hDensity)
      (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) := by
  let U := presentedPullbackVolumeObject hc C F ω h δ hDensity
  let V : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc F,ω⟩
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient
    (canonicalRVIso hc (Section6.pullbackPresentationIso h))
  apply RVVolumeIso.of_preserving_coordinates_full hc C e
  · intro u
    exact pullbackPresentation_volume h ⟨u.val,u.property⟩
  · intro u
    exact (hDensity (finiteIsoMap e u)).trans
      (congrFun (Section6.pullbackPresentationIso_labels h ⟨u.val,u.property⟩) δ)

end IntegrationInACVF.Section7
