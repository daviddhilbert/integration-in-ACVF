import IntegrationSection6.GammaDegreeTransport
import IntegrationSection6.GammaSwappedVolumes

/-! Swapping two blocks of volume coordinates preserves the common-blowup
relation, using the actual weight-preserving identity-label isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n e : ℕ}

def gammaSwapVolumeCastIso (U : GammaRVFiniteObject B (n+e)) :
    GammaRVIso U.toGammaRVObject (gammaCastDegree (Nat.add_comm e n) (gammaSwapVolumeBlocks U)).toGammaRVObject := by
  apply gammaIsoOfEqualDegreeEquiv (Nat.add_comm n e) U (gammaSwapVolumeBlocks U) (Equiv.refl _) (FiniteRV.gammaIsoRefl U).graph
  intro u
  change rawWeight (fun j => (gammaVolumeValue U.toGammaRVObject u j).val) =
    rawWeight (fun j => (gammaVolumeValue U.toGammaRVObject u ((@finAddFlip e n) j)).val)
  unfold rawWeight
  exact (Fintype.sum_equiv (@finAddFlip e n) _ _ (fun j => rfl)).symm

theorem FiniteRV.GammaIsp.swapVolumeBlocks {κ : Cardinal}
    {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ} {h00 : M ⊨ Axioms.ACVF00}
    {hreal : Cardinal.mk B.real < κ} {U V : GammaRVFiniteObject B (n+e)}
    (H : FiniteRV.GammaIsp hκ hs h00 hreal U V) :
    FiniteRV.GammaIsp hκ hs h00 hreal (gammaSwapVolumeBlocks U) (gammaSwapVolumeBlocks V) := by
  have h := H.corollary_6_6 (FiniteRV.gammaIsoSymm (gammaSwapVolumeCastIso U))
    (FiniteRV.gammaIsoSymm (gammaSwapVolumeCastIso V))
  have h' := h.castDegree (Nat.add_comm n e)
  simpa only [gammaCastDegree_symm] using h'

theorem FiniteRV.GammaIsp.of_swapVolumeBlocks {κ : Cardinal}
    {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ} {h00 : M ⊨ Axioms.ACVF00}
    {hreal : Cardinal.mk B.real < κ} {U V : GammaRVFiniteObject B (n+e)}
    (H : FiniteRV.GammaIsp hκ hs h00 hreal (gammaSwapVolumeBlocks U) (gammaSwapVolumeBlocks V)) :
    FiniteRV.GammaIsp hκ hs h00 hreal U V := by
  have h := H.castDegree (Nat.add_comm e n)
  exact h.corollary_6_6 (gammaSwapVolumeCastIso U) (gammaSwapVolumeCastIso V)

end IntegrationInACVF.Section6
