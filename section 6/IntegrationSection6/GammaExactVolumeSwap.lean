import IntegrationSection6.GammaSwappedVolumes
import IntegrationSection6.FiniteGammaIsoLaws

/-! Exact volume-preserving maps remain exact after swapping volume blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n k : ℕ} {U V : GammaRVFiniteObject B (n+k)}

def gammaSwapExactVolumeIso (f : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (hf : ∀ u, gammaVolumeValue V.toGammaRVObject (f.equiv u) = gammaVolumeValue U.toGammaRVObject u) :
    GammaRVIso (gammaSwapVolumeBlocks U).toGammaRVObject (gammaSwapVolumeBlocks V).toGammaRVObject := by
  apply gammaIsoOfFiniteEquiv (gammaSwapVolumeBlocks U) (gammaSwapVolumeBlocks V) f.equiv f.graph
  intro u
  exact congrArg (fun z : Fin (n+k) → RV (M := M) =>
    rawWeight (fun j => (z ((@finAddFlip k n) j)).val)) (hf u).symm

theorem gammaSwapExactVolumeIso_volume (f : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (hf : ∀ u, gammaVolumeValue V.toGammaRVObject (f.equiv u) = gammaVolumeValue U.toGammaRVObject u)
    (u : rvObjectDomain U.object) :
    gammaVolumeValue (gammaSwapVolumeBlocks V).toGammaRVObject ((gammaSwapExactVolumeIso f hf).equiv u) =
      gammaVolumeValue (gammaSwapVolumeBlocks U).toGammaRVObject u :=
  congrArg (fun z => z ∘ (@finAddFlip k n)) (hf u)

end IntegrationInACVF.Section6.FiniteRV
