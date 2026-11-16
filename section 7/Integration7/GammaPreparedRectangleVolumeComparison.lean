module

public import Integration7.PreparedRectangleFiniteVolumes
public import Integration7.LabelDeterminedPullbackGamma
public import Integration7.PreparedRectangleVolumeComparison

@[expose] public section

/-! Original-Gamma certificate for volume descent through the actual
prepared rectangle conjugate. -/
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
theorem volumeIsoOfConjugate_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
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
    (volumeIsoOfConjugate hc C hGC PV PH v hv h hh hvΓ hhΓ hvLabels hhLabels hvJ hhJ
      hfin δ hδ hSource hTarget hNZV hNZH).GammaDefinable G := by
  unfold volumeIsoOfConjugate
  apply pullbackVolumeIsoOfLabelDeterminedMap_gamma
  · exact hGC
  · exact PV.conjugate_gamma PH v hv h hvΓ hhΓ
  · exact PV.volume_target_gamma

end IntegrationInACVF.Section7.RectangleFamilyPullbackPreparation
