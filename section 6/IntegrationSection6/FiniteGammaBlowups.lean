import IntegrationSection6.FiniteGammaWeightedIsos
import IntegrationSection6.FiniteGammaElementaryAt
import IntegrationSection6.FiniteGammaLiftGluing
import IntegrationSection6.BlowupPresentations
import Section7.GammaLiftEquivalence

/-! Gamma-certified blowups in RV[k], retaining actual split charts.
The real presentation supports the maps, while every chart graph remains
over B. Forgetting certificates gives a genuine Definition6.1 blowup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure GammaBlowupAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U V : GammaObjectAt B S n) where
  center : GammaObjectAt B S n
  remainder : GammaObjectAt B S n
  coordinate : Fin n
  admissible : GammaAdmissible center.toGamma.toGammaRVObject coordinate
  source : GammaIsoAt U (gammaCoprodAt center remainder)
  result : GammaIsoAt V (gammaCoprodAt (gammaElementaryAt hκ hs h00 hsmall  center coordinate admissible) remainder)

namespace GammaBlowupAt
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

variable {U V : GammaObjectAt B S n} (H : GammaBlowupAt hκ hs h00 hsmall  U V)

def toBlowup : @Blowup M N hN S n U.object V.object := by
  let es := isoAtAmbient H.source.iso
  let et := isoAtAmbient H.result.iso
  have hAd := H.admissible.ordinary hκ hs h00 hsmall
  let i := H.coordinate
  letI := N
  letI := hN
  exact IntegrationInACVF.Section6.Blowup.of_split i hAd es et

include H in
/-- The arbitrary-chart part uses the checked original-Gamma lifting
 theorem, with its canonical-totalization hypothesis stated explicitly. -/
theorem liftIso (hcan : CanonicalStructure.IsCanonical (M := M)) (hB : VFGammaGeneratedBase B) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  obtain ⟨es⟩ := SpecialTransformations.Section7.GammaRVIso.liftIso hcan hκ hs h00 hsmall hB H.source.toGamma
  obtain ⟨et⟩ := SpecialTransformations.Section7.GammaRVIso.liftIso hcan hκ hs h00 hsmall hB H.result.toGamma
  obtain ⟨ec⟩ := gammaElementaryAt_liftIso hκ hs h00 hsmall hB H.center H.coordinate H.admissible
  let er := gammaIso_reflexive H.remainder.toGamma.lift H.remainder.toGamma.toGammaRVObject.lift_definable
  let e := gammaCoprodLiftIso ec er
  exact ⟨(es.trans (gammaLogicInput B) e).trans (gammaLogicInput B) (et.symm (gammaLogicInput B))⟩

end GammaBlowupAt
end IntegrationInACVF.Section6.FiniteRV
