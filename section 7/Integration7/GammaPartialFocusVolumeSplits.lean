module

public import Integration7.GammaFullFocusVolumeComparison
public import Integration7.GammaComplementVolumeComparison
public import Integration7.GammaVolumePullbackPartitions
public import Integration7.VolumePartialFocusImages
public import IntegrationSection6.FiniteGammaPartialCharts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A partial last-coordinate focus has genuine volume blowup split
charts over the original Gamma base, with its inactive labels unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

set_option maxHeartbeats 1200000 in
theorem gamma_partial_focus_volume_split
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    {j : Fin (rvObjectArity U.object.obj)} (D : Focus A (Fin.last k) j)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaFocusDefinable B D)
    (δ : Fin (rvObjectArity U.object.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    let L := focusActiveSet D
    let LD := liftLabelLocus L
    let hLD := liftLabelLocus_subset h (focusActiveSet_subset D)
    let hLΓ := (gammaActiveRVObject h D U.real_contains hA hD).domain_graph
    let V := FiniteRV.gammaRestrictAt U LD hLD hLΓ
    let Ω : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc U.object,ω⟩
    let LV := Ω.restrict (canonicalRawRVDomain hc LD) hLD
    let RV := Ω.restrict (Ω.underlying.obj.domain.sdiff (canonicalRawRVDomain hc LD)) Set.sdiff_subset
    ∃ hAd : GammaAdmissible V.toGamma.toGammaRVObject (Fin.last k),
    ∃ eS : RVVolumeIso Ω (LV.coprod RV),
    ∃ eT : RVVolumeIso (partialFocusVolumeImage hc C U.object ω h D δ hDensity)
      ((elementaryVolumeObject C LV (canonicalGammaElementaryAdmissible hc C V LV.form hAd)).coprod RV),
      eS.GammaDefinable B ∧ eT.GammaDefinable B := by
  intro L LD hLD hLΓ V Ω LV RV
  let R := focusInactiveSet D
  have hsmall := (Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small
  have hAd : GammaAdmissible V.toGamma.toGammaRVObject (Fin.last k) :=
    gammaActiveRVObject_admissible h D C.uncountable.le C.saturated hsmall U.real_contains hA hD
  have hAP := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A) h)
  have hLP := focusActiveSet_pullback D hAP
  have hRP := focusInactiveSet_pullback D hAP
  have hPart := partialFocus_source_partition D
  have hDisj : Disjoint (carrier L) (carrier R) := Set.disjoint_left.mpr (fun p hp hq => hq.2 hp)
  have hL : GammaSetDefinable B (carrier L) := gamma_focusActiveSet D hA hD
  have hR : GammaSetDefinable B (carrier R) := (gammaLogicInput B).sdiff hA hL
  have hTL := GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal (activeFocus D))
    ⟨hL,gamma_activeFocus D hA hD⟩
  have hTA := GammaPrimitiveDefinable.target (gammaLogicInput B) (.centripetal D) ⟨hA,hD⟩
  let T := FiniteRV.gammaFullFocusImageAt C.uncountable.le C.saturated C.model00 hsmall
    V (focusActiveRVObject_presents h D) (activeFocus D) (activeFocus_full D) hAd hL
    (gamma_activeFocus D hA hD)
  let Q := FiniteRV.gammaComplementPresentationAt U h hPart hDisj hLP hRP hLΓ hR
  have hNZ := focus_density_label_nonzero D δ
    (lift_density_label_nonzero Ω (canonicalRVObject_presentsLift hc h) δ hDensity)
  have hImagePart := partialFocus_image_partition D
  let PVL := pullbackCoordinateVolumeObject hc (activeFocus D).etaImage T.object.property δ
    (fun p => hNZ ⟨p.val,(Set.ext_iff.mp hImagePart p.val).mpr (Or.inl p.property)⟩)
  let PVR := pullbackCoordinateVolumeObject hc R Q.object.property δ
    (fun p => hNZ ⟨p.val,(Set.ext_iff.mp hImagePart p.val).mpr (Or.inr p.property)⟩)
  have hDensityL : ∀ u, LV.form.value u = u.val δ := fun u => hDensity ⟨u.val,hLD u.property⟩
  obtain ⟨eL,heL⟩ := gamma_full_focus_volume_comparison hc C V LV.form
    (focusActiveRVObject_presents h D) (activeFocus D) (activeFocus_full D) hAd hL
    (gamma_activeFocus D hA hD) δ hDensityL PVL.form (fun _ => rfl)
  obtain ⟨eR,heR⟩ := gamma_complement_volume_comparison hc C U ω h hPart hDisj hLP hRP
    hLΓ hR δ hDensity PVR.form (fun _ => rfl)
  let ep := pullbackVolumePartitionIso hc C D.etaImage (activeFocus D).etaImage R
    (partialFocusImage_finite C U.object h D) T.object.property Q.object.property hImagePart
    (partialFocus_image_disjoint D) ((activeFocus D).etaImage_pullback hLP) δ hNZ
  have hep : ep.GammaDefinable B := gamma_pullback_volume_partition hc C D.etaImage
    (activeFocus D).etaImage R (partialFocusImage_finite C U.object h D) T.object.property Q.object.property
    hImagePart (partialFocus_image_disjoint D) ((activeFocus D).etaImage_pullback hLP) δ hNZ
    U.real_contains hTA hTL hR
  let es := (volumeComplementPartitionIso hc C Ω (canonicalRawRVDomain hc LD) hLD).symm hc C
  let et := (ep.symm hc C).trans hc C (eL.coprod hc C eR)
  exact ⟨hAd,es,et,
    (gamma_volume_complement_partition hc C U ω LD hLD hLΓ).symm hc C B,
    (hep.symm hc C B).trans hc C B (heL.coprod hc C B heR)⟩

end IntegrationInACVF.Section7
