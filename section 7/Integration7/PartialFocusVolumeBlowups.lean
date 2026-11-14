import Integration7.VolumePartialFocusImages
import Integration7.VolumePullbackPresentations
import Integration7.VolumePullbackPartitions
import Integration7.VolumeObjectPartitions
import Integration7.IteratedVolumeBlowups
import IntegrationSection6.LiftLabelPartitions
import IntegrationSection6.PartialFocusPartition

/-! An arbitrary last-coordinate focus gives one actual volume blowup:
blow up its active old-label locus and keep the complementary labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Focus carrier pullbackObject rvObjectArity)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def partialFocusVolumeBlowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : @RVFiniteObject M N (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc F).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity F.obj)}
    (h : @Section6.PresentsLift M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A))
    {j : Fin (rvObjectArity F.obj)} (D : Focus A (Fin.last k) j)
    (δ : Fin (rvObjectArity F.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    VolumeBlowup (⟨canonicalFiniteRVObject hc F,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (partialFocusVolumeImage hc C F ω h D δ hDensity) := by
  let U : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc F,ω⟩
  let L := Section6.focusActiveSet D
  let R := Section6.focusInactiveSet D
  have hAP := (Section6.pullback_normalize (carrier A)).mp
    (@Section6.PresentsLift.pullback M N hN (C.base : Set M) (k+1) F.obj (Section6.normalizedPointSet A) h)
  have hLP := Section6.focusActiveSet_pullback D hAP
  have hRP := Section6.focusInactiveSet_pullback D hAP
  have hp := Section6.partialFocus_source_partition D
  have hd : Disjoint (carrier L) (carrier R) :=
    Set.disjoint_left.mpr (fun p hl hr => hr.2 hl)
  have hLA : carrier L ⊆ carrier A := Section6.focusActiveSet_subset D
  have hRA : carrier R ⊆ carrier A := fun _ hp => hp.1
  let LD := canonicalRawRVDomain hc (Section6.liftLabelLocus L)
  let RD := canonicalRawRVDomain hc (Section6.liftLabelLocus R)
  have hLD : LD.carrier ⊆ U.underlying.obj.domain.carrier := Section6.liftLabelLocus_subset h hLA
  have hRD : RD.carrier ⊆ U.underlying.obj.domain.carrier := Section6.liftLabelLocus_subset h hRA
  let LV := U.restrict LD hLD
  let RV := U.restrict RD hRD
  let LF : @RVFiniteObject M N (C.base : Set M) (k+1) :=
    ⟨Section6.focusActiveRVObject h D,
      @RVObject.restrict_finite_volume M N (C.base : Set M) (k+1) F.obj F.property _ _⟩
  let RF : @RVFiniteObject M N (C.base : Set M) (k+1) :=
    ⟨@RVObject.restrict M N (C.base : Set M) (k+1) F.obj (Section6.liftLabelLocus R)
        (Section6.liftLabelLocus_subset h hRA),
      @RVObject.restrict_finite_volume M N (C.base : Set M) (k+1) F.obj F.property _ _⟩
  have hLRep := Section6.focusActiveRVObject_presents h D
  have hRRep := Section6.normalizedPresentsLift_sublocus h hRA hRP
  let ωL : VolumeForm (canonicalFiniteRVObject hc LF).obj.domain := LV.form
  let ωR : VolumeForm (canonicalFiniteRVObject hc RF).obj.domain := RV.form
  have hDenL : ∀ u, ωL.value u = u.val δ := fun u => hDensity ⟨u.val,hLD u.property⟩
  have hDenR : ∀ u, ωR.value u = u.val δ := fun u => hDensity ⟨u.val,hRD u.property⟩
  have hLF := partialFocusImage_finite C LF hLRep (Section6.activeFocus D)
  have hRF := (@Section6.finite_volume_iso M N hN (C.base : Set M) (k+1) (pullbackObject R) RF.obj
    (Section6.pullbackPresentationIso hRRep)).mpr RF.property
  have hNZ := focus_density_label_nonzero D δ
    (lift_density_label_nonzero U (canonicalRVObject_presentsLift hc h) δ hDensity)
  let V := partialFocusVolumeImage hc C F ω h D δ hDensity
  have hPart := Section6.partialFocus_image_partition D
  have hDisj := Section6.partialFocus_image_disjoint D
  have hImageLP := (Section6.activeFocus D).etaImage_pullback hLP
  let PVL := pullbackCoordinateVolumeObject hc (Section6.activeFocus D).etaImage hLF δ
    (fun p => hNZ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inl p.property)⟩)
  let PVR := pullbackCoordinateVolumeObject hc R hRF δ
    (fun p => hNZ ⟨p.val,(Set.ext_iff.mp hPart p.val).mpr (Or.inr p.property)⟩)
  let b := focusActiveVolumeBlowup hc C F ω h D
  let BV := fullFocusPresentedVolumeObject hc C LV (focusActiveVolumeObject_presents hc C F ω h D)
    (Section6.activeFocus D) (Section6.activeFocus_full D) (focusActiveVolumeObject_admissible hc C F ω h D)
  let eL : PVL.underlying ≅ BV.underlying := rvFiniteIsoOfAmbient (Iso.refl PVL.underlying.obj)
  let iL : RVVolumeIso PVL BV := RVVolumeIso.of_preserving_coordinates_full hc C eL (fun _ => rfl) (by
    intro u
    exact fullFocusPresentedVolumeObject_density_label hc C LV
      (focusActiveVolumeObject_presents hc C F ω h D) (Section6.activeFocus D) (Section6.activeFocus_full D)
      (focusActiveVolumeObject_admissible hc C F ω h D) δ hDenL ⟨u.val,u.property⟩)
  let iR : RVVolumeIso PVR RV := pullbackVolumePresentationIso hc C RF ωR hRRep δ hDenR
  let ep := pullbackVolumePartitionIso hc C D.etaImage (Section6.activeFocus D).etaImage R
    (partialFocusImage_finite C F h D) hLF hRF hPart hDisj hImageLP δ hNZ
  exact {
    locus := LV
    complement := RV
    blownLocus := BV
    elementary := b
    sourceIso := volumeObjectPartitionIso hc C U LD RD hLD hRD
      (Section6.liftLabelLoci_cover h hp) (Section6.liftLabelLoci_disjoint h hLA hRA hd hLP)
    targetIso := (ep.symm hc C).trans hc C (iL.coprod hc C iR) }

end IntegrationInACVF.Section7
