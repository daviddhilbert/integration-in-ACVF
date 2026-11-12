import IntegrationSection6.GammaBasicAdmissibility
import IntegrationSection6.FiniteGammaElementaryFactors
import IntegrationSection6.FiniteGammaProductCoherence
import IntegrationSection6.FiniteGammaProductUnit
import IntegrationSection6.FiniteGammaProductIsos
import IntegrationSection6.FiniteGammaGenerators

/-! The basic degree-one elementary replacement is a genuine Gamma
common-blowup relation. The positive parameter object includes zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}
local notation "N" => (@CanonicalStructure.normalize M sM)

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)

def gammaDeletedOneIsoUnit (hBS : B.real ⊆ S) :
    GammaIsoAt (gammaDeleteVolumeAt hκ hs h00 hsmall (gammaOneAt hBS) 0 (gammaOneAt_admissible hBS)) (gammaUnitAt hBS) := by
  let V := gammaDeleteVolumeAt hκ hs h00 hsmall (gammaOneAt hBS) 0 (gammaOneAt_admissible hBS)
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) S)
  exact GammaIsoAt.ofAmbientFormula
    (@rvIsoOfVolumePreservingBijection M N S 0 V.object.obj (gammaUnitAt hBS).object.obj F
      Function.bijective_id (fun _ => funext (fun j : Fin 0 => j.elim0)))
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real))
    (fun _ => rfl)

def gammaBasicElementaryIsoPositive (hBS : B.real ⊆ S) :
    GammaIsoAt (gammaElementaryAt hκ hs h00 hsmall (gammaOneAt hBS) 0 (gammaOneAt_admissible hBS))
      (gammaPositiveAt hBS) := by
  let P := gammaPositiveAt hBS
  let Z := gammaUnitAt hBS
  let E := gammaAdmissibleFactorPositive hκ hs h00 hsmall (gammaOneAt hBS) 0 (gammaOneAt_admissible hBS)
  let D := gammaDeletedOneIsoUnit hκ hs h00 hsmall hBS
  let F := E.trans (gammaProductIsoAt D (GammaIsoAt.refl P))
  let G := gammaProductCommReindexedIsoAt Z P
  let H := gammaReindexVolumeIsoAt (gammaProductAt P Z) (@finAddFlip 0 1)
  exact ((F.trans G).trans H.symm).trans (gammaProductRightUnitIsoAt P)

theorem gammaBasic_ispAt (hBS : B.real ⊆ S) :
    GammaIspAt hκ hs h00 hsmall (gammaOneAt hBS) (gammaPositiveAt hBS) :=
  (gammaElementary_ispAt hκ hs h00 hsmall (gammaOneAt hBS) 0 (gammaOneAt_admissible hBS)).corollary_6_6
    (GammaIsoAt.refl _) (gammaBasicElementaryIsoPositive hκ hs h00 hsmall hBS).symm

end IntegrationInACVF.Section6.FiniteRV
