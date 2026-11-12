import IntegrationSection6.GammaVolumeProjections
import IntegrationSection6.FiniteCoordinateDeletion
import IntegrationSection6.GammaFiniteSlices
import IntegrationSection6.FiniteGammaObjects

/-! Deleting an admissible volume coordinate keeps the actual object
in RV[k-1]. Finiteness uses the original-base algebraic label slices,
with no cardinal bound on the presentation codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}

def gammaDeleteVolume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaRVFiniteObject B (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGammaRVObject i) : GammaRVFiniteObject B n where
  toGammaRVObject := gammaProjectVolumeObject U.toGammaRVObject i.succAbove
  finite_volume := by
    intro t
    let f := gammaVolumeValue U.toGammaRVObject
    have hf (r : Fin (n+1) → RV (M := M)) : {u : rvObjectDomain U.object | f u = r}.Finite := by
      apply (U.finite_volume ⟨r,Set.mem_univ _⟩).subset
      intro u hu
      exact Subtype.ext hu
    let z : RV (M := M) := ⟨iRVZero,SpecialTransformations.Milestone0.Transfer.rv_zero_mem hM⟩
    have h := finite_fibres_coordinate_deletion f i z hf (hAd.finite_label_slices hκ hs h00 hsmall) t.val
    apply h.subset
    intro u hu
    exact congrArg Subtype.val hu

def gammaDeleteVolumeAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) : GammaObjectAt B S n :=
  gammaObjectAtExtend (gammaDeleteVolume hκ hs h00 hsmall U.toGamma i hAd) (Set.Subset.refl S)

end IntegrationInACVF.Section6.FiniteRV
