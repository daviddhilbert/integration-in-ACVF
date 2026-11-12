import IntegrationSection6.NativeGammaRVIsoLifts
import IntegrationSection6.FiniteGammaCommonBlowups

/-! Corollary6.13 and common-blowup lift invariance in the actual RV[k]
categories, with the presentation hypothesis removed. The genuine
VF/Gamma-generation hypothesis is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
variable {h00 : M ⊨ Axioms.ACVF00} {hreal : Cardinal.mk B.real < κ}

theorem GammaBlowupAt.liftIsoNative {U V : GammaObjectAt B S k}
    (H : GammaBlowupAt hκ hs h00 hreal U V) (hB : VFGammaGeneratedBase B) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  obtain ⟨es⟩ := gammaRVIso_liftIso hκ hs h00 hreal hB H.source.toGamma
  obtain ⟨et⟩ := gammaRVIso_liftIso hκ hs h00 hreal hB H.result.toGamma
  obtain ⟨ec⟩ := gammaElementaryAt_liftIso hκ hs h00 hreal hB H.center H.coordinate H.admissible
  let er := gammaIso_reflexive H.remainder.toGamma.lift H.remainder.toGamma.toGammaRVObject.lift_definable
  let e := gammaCoprodLiftIso ec er
  exact ⟨(es.trans (gammaLogicInput B) e).trans (gammaLogicInput B) (et.symm (gammaLogicInput B))⟩

theorem GammaIteratedBlowup.liftIsoNative {r : ℕ} {U V : GammaObjectAt B S k}
    (H : GammaIteratedBlowup hκ hs h00 hreal r U V) (hB : VFGammaGeneratedBase B) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  induction H with
  | zero he =>
    obtain ⟨e⟩ := he
    exact gammaRVIso_liftIso hκ hs h00 hreal hB e.toGamma
  | cons he _ ih =>
    obtain ⟨e⟩ := he
    obtain ⟨f⟩ := e.liftIsoNative hB
    obtain ⟨g⟩ := ih
    exact ⟨f.trans (gammaLogicInput B) g⟩

theorem GammaIspAt.liftIsoNative {U V : GammaObjectAt B S k}
    (H : GammaIspAt hκ hs h00 hreal U V) (hB : VFGammaGeneratedBase B) :
    Nonempty (GammaIso B U.toGamma.lift V.toGamma.lift) := by
  obtain ⟨r,s,A,C,hU,hV,⟨e⟩⟩ := H
  obtain ⟨f⟩ := hU.liftIsoNative hB
  obtain ⟨g⟩ := hV.liftIsoNative hB
  obtain ⟨h⟩ := gammaRVIso_liftIso hκ hs h00 hreal hB e.toGamma
  exact ⟨(f.trans (gammaLogicInput B) h).trans (gammaLogicInput B) (g.symm (gammaLogicInput B))⟩

theorem GammaIsp.liftIsoNative {U V : GammaRVFiniteObject B k}
    (H : GammaIsp hκ hs h00 hreal U V) (hB : VFGammaGeneratedBase B) :
    Nonempty (GammaIso B U.lift V.lift) := by
  obtain ⟨R,hUR,hVR,H⟩ := H
  exact H.liftIsoNative hB

end IntegrationInACVF.Section6.FiniteRV
