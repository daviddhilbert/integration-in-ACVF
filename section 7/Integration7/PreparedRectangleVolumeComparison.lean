import Integration7.PreparedRectangleFiniteVolumes
import Integration7.LabelDeterminedPullbackDescent

/-! Full RV volume descent for the actual conjugate of two specified
rectangle preparations, with arbitrary retained coordinate density.
Finiteness and density nonvanishing come from the original family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.RectangleFamilyPullbackPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

set_option maxHeartbeats 2400000 in
def volumeIsoOfConjugate (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    {H V W : DefSet (M := M) (C.base : Set M) 2 m}
    (PV : RectangleFamilyPullbackPreparation G V) (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W) (hh : Function.Bijective h)
    (hvΓ : GammaGraphDefinable G (pointMapGraph v)) (hhΓ : GammaGraphDefinable G (pointMapGraph h))
    (hvLabels : ∀ p : H, (v p).val.2 = p.val.2) (hhLabels : ∀ p : H, (h p).val.2 = p.val.2)
    (hvJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc v) p 1))
    (hhJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc h) p 1))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (δ : Fin m) (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero)
    (hSource : ∀ p q : PV.volumeTarget,
      p.val.2 ∘ PV.volumeLabelIndex = q.val.2 ∘ PV.volumeLabelIndex → SameRV p.val q.val)
    (hTarget : ∀ p q : PH.volumeTarget,
      p.val.2 ∘ PH.volumeLabelIndex = q.val.2 ∘ PH.volumeLabelIndex → SameRV p.val q.val)
    (hNZV : ∀ p : PV.volumeTarget, ∀ i, vfAt p.val i ≠ 0)
    (hNZH : ∀ p : PH.volumeTarget, ∀ i, vfAt p.val i ≠ 0) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let hAF := PV.finite_volume C.uncountable.le C.saturated hsmall v hv hvΓ hfin
    let hBF := PH.finite_volume C.uncountable.le C.saturated hsmall h hh hhΓ hfin
    let hδV := PV.retained_density_nonzero v hv hvLabels δ hδ
    let hδH := PH.retained_density_nonzero h hh hhLabels δ hδ
    RVVolumeIso (pullbackCoordinateVolumeObject hc PV.volumeTarget hAF (PV.volumeLabelIndex δ) hδV)
      (pullbackCoordinateVolumeObject hc PH.volumeTarget hBF (PH.volumeLabelIndex δ) hδH) := by
  intro hsmall hAF hBF hδV hδH
  let f := PV.conjugate PH v hv h
  have hf := PV.conjugate_bijective PH v hv h hh
  have hLabels := PV.conjugate_old_labels PH v hv h hvLabels hhLabels
  have hJ := PV.conjugate_jacobian_one hc C PH v hv h hh hvJ hhJ
  have hMeasure : PreservesVFVolume
      (rawPullbackVolumeForm hc PV.volumeTarget PV.volume_target_pullback hAF (PV.volumeLabelIndex δ) hδV)
      (rawPullbackVolumeForm hc PH.volumeTarget PH.volume_target_pullback hBF (PH.volumeLabelIndex δ) hδH)
      (rawSpecialMap hc f) := by
    apply hJ.mono
    intro p hp
    refine ⟨1,hp,?_⟩
    rw [RVOperations.rv_one,mul_one,rawPullbackVolumeForm_density,rawPullbackVolumeForm_density]
    exact (congrFun (hLabels p) δ).symm
  exact pullbackVolumeIsoOfLabelDeterminedMap hc C PV.volumeTarget PH.volumeTarget
    PV.volume_target_pullback PH.volume_target_pullback hAF hBF
    (PV.volumeLabelIndex δ) (PH.volumeLabelIndex δ) hδV hδH
    PV.volumeLabelIndex PH.volumeLabelIndex hSource hTarget
    (fun p i he => hNZV p i ((CanonicalRV.encodedRv_zero_iff _).mp he))
    (fun p i he => hNZH p i ((CanonicalRV.encodedRv_zero_iff _).mp he))
    f hf hLabels hMeasure

end IntegrationInACVF.Section7.RectangleFamilyPullbackPreparation
