import IntegrationSection6.FiniteGammaUniversalCharts

/-! Common blowups can always be represented over the common internal
universe, with their original Gamma certificates unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}
variable {h00 : M ⊨ Axioms.ACVF00} {hreal : Cardinal.mk B.real < κ}

theorem GammaIsp.at_univ {U V : GammaRVFiniteObject B n} (H : GammaIsp hκ hs h00 hreal U V) :
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject U) (gammaUniversalObject V) := by
  obtain ⟨R,hUR,hVR,H⟩ := H
  exact H.extend (Set.subset_univ _)

theorem GammaIspAt.to_global {U V : GammaObjectAt B S n} (H : GammaIspAt hκ hs h00 hreal U V) :
    GammaIsp hκ hs h00 hreal U.toGamma V.toGamma :=
  ⟨S,Set.Subset.refl _,Set.Subset.refl _,H⟩

end IntegrationInACVF.Section6.FiniteRV
