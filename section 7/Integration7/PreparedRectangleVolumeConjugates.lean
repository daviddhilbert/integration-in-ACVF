import Integration7.RectangleFamilyVolumePreparations
import IntegrationSection5.GammaGraphOperations

/-! The actual conjugate between two prepared rectangle targets.
Every map is specified: the two original bijections and the two
relative-special preparations. Shared labels and Jacobian one pass
through the entire composition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

theorem native_inverse_bijective {n a u b : ℕ}
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S u b}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (Map.inverse f hf) := by
  constructor
  · intro p q he
    have h := congrArg f he
    simpa only [Map.apply_inverse] using h
  · intro p
    exact ⟨f p,Map.inverse_apply f hf p⟩

namespace RectangleFamilyPullbackPreparation
variable {H V W : DefSet (M := M) S 2 m}

def conjugate (PV : RectangleFamilyPullbackPreparation G V)
    (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W) :
    Map PV.volumeTarget PH.volumeTarget :=
  Map.comp PH.volumeMap (Map.comp h
    (Map.comp (Map.inverse v hv) (Map.inverse PV.volumeMap PV.volume_map_bijective)))

theorem conjugate_bijective (PV : RectangleFamilyPullbackPreparation G V)
    (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W) (hh : Function.Bijective h) :
    Function.Bijective (PV.conjugate PH v hv h) :=
  PH.volume_map_bijective.comp (hh.comp
    ((native_inverse_bijective v hv).comp (native_inverse_bijective _ PV.volume_map_bijective)))

theorem conjugate_gamma (PV : RectangleFamilyPullbackPreparation G V)
    (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W)
    (hvΓ : GammaGraphDefinable G (pointMapGraph v))
    (hhΓ : GammaGraphDefinable G (pointMapGraph h)) :
    GammaGraphDefinable G (pointMapGraph (PV.conjugate PH v hv h)) :=
  gamma_composition_graph _ _
    (gamma_composition_graph _ _
      (gamma_composition_graph _ _
        (gamma_inverse_map_graph _ PV.volume_map_bijective PV.volume_graph_gamma)
        (gamma_inverse_map_graph v hv hvΓ)) hhΓ) PH.volume_graph_gamma

theorem conjugate_old_labels (PV : RectangleFamilyPullbackPreparation G V)
    (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W)
    (hvLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (hhLabels : ∀ p : H, (h p).val.2 = p.val.2)
    (p : PV.volumeTarget) :
    (PV.conjugate PH v hv h p).val.2 ∘ PH.volumeLabelIndex = p.val.2 ∘ PV.volumeLabelIndex := by
  let a := Map.inverse PV.volumeMap PV.volume_map_bijective p
  let b := Map.inverse v hv a
  have hba : b.val.2 = a.val.2 := by
    have h := hvLabels b
    rw [Map.apply_inverse] at h
    exact h.symm
  funext i
  change (PH.volumeMap (h b)).val.2 (PH.volumeLabelIndex i) = p.val.2 (PV.volumeLabelIndex i)
  rw [PH.volume_old_labels,hhLabels,hba]
  have h := PV.volume_old_labels a i
  rw [Map.apply_inverse] at h
  exact h.symm

set_option maxHeartbeats 2000000 in
theorem conjugate_jacobian_one (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {H V W : DefSet (M := M) (C.base : Set M) 2 m}
    (PV : RectangleFamilyPullbackPreparation G V) (PH : RectangleFamilyPullbackPreparation G W)
    (v : Map H V) (hv : Function.Bijective v) (h : Map H W) (hh : Function.Bijective h)
    (hvJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc v) p 1))
    (hhJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc h) p 1)) :
    VFAlmostEverywhere (rawSpecialSet hc PV.volumeTarget)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (PV.conjugate PH v hv h)) p 1) := by
  have h1 := vfJacobianOne_comp hc C (by decide : 0 < 2)
    (rawSpecialMap hc (Map.inverse PV.volumeMap PV.volume_map_bijective))
    (rawSpecialMap hc (Map.inverse v hv))
    (native_inverse_bijective _ PV.volume_map_bijective).1
    (PV.volume_inverse_jacobian_one hc C) (vfJacobianOne_inverse hc C (by decide) _ hv hvJ)
  have h2 := vfJacobianOne_comp hc C (by decide : 0 < 2) _ (rawSpecialMap hc h)
    ((native_inverse_bijective v hv).1.comp
      (native_inverse_bijective _ PV.volume_map_bijective).1) h1 hhJ
  exact vfJacobianOne_comp hc C (by decide : 0 < 2) _ (rawSpecialMap hc PH.volumeMap)
    (hh.1.comp ((native_inverse_bijective v hv).1.comp
      (native_inverse_bijective _ PV.volume_map_bijective).1)) h2 (PH.volume_jacobian_one hc C)

end RectangleFamilyPullbackPreparation
end IntegrationInACVF.Section7
