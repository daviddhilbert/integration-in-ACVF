module

public import Integration7.PreparedRectangleVolumeConjugates
public import IntegrationSection6.GammaFiniteMixedBijections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Finite volume fibres and literal coordinate densities for the
actual prepared targets follow from their original Gamma bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.RectangleFamilyPullbackPreparation
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {H V : DefSet (M := M) S 2 m}

theorem finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    (PV : RectangleFamilyPullbackPreparation G V)
    (v : Map H V) (hv : Function.Bijective v) (hvΓ : GammaGraphDefinable G (pointMapGraph v))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite) :
    @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject PV.volumeTarget)) :=
  pullbackObject_finiteVolume _ PV.volume_target_pullback
    (finite_rv_fibres_of_gamma_bijection hκ hs hsmall (Map.comp PV.volumeMap v)
      (PV.volume_map_bijective.comp hv) (gamma_composition_graph _ _ hvΓ PV.volume_graph_gamma) hfin)

theorem retained_density_nonzero (PV : RectangleFamilyPullbackPreparation G V)
    (v : Map H V) (hv : Function.Bijective v) (hvLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (δ : Fin m) (hδ : ∀ p : H, (p.val.2 δ).val ≠ iRVZero)
    (q : PV.volumeTarget) : (q.val.2 (PV.volumeLabelIndex δ)).val ≠ iRVZero := by
  let a := Map.inverse PV.volumeMap PV.volume_map_bijective q
  let b := Map.inverse v hv a
  have ha := PV.volume_old_labels a δ
  rw [Map.apply_inverse] at ha
  have hb := hvLabels b
  rw [Map.apply_inverse] at hb
  have he : q.val.2 (PV.volumeLabelIndex δ) = b.val.2 δ := ha.trans (congrFun hb δ)
  exact he ▸ hδ b

end IntegrationInACVF.Section7.RectangleFamilyPullbackPreparation
