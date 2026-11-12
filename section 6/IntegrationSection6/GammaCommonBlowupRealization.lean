import IntegrationSection6.GammaCommonBlowupSchemata
import IntegrationSection6.GammaChainRealization
import IntegrationSection6.FiniteGammaCommonBlowups

/-! Valid finite common-blowup schemata realize genuine original-Gamma
common forward blowups in RV[k], at their exact encoded chain lengths. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}
variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}
open FiniteRV

theorem GammaFiniteCommonSchema.realizeAt {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteCommonSchema U V)
    (z : Fin p → M) (hz : H.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (U.rowDomain z) (U.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (V.rowDomain z) (V.rowVolume z)) :
    GammaIspAt hκ hs h00 (small_union_range hκ B.real hreal z)
      (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  obtain ⟨LP⟩ := H.leftObject.realize z hz.1
  obtain ⟨RP⟩ := H.rightObject.realize z hz.2.1
  have hL := H.leftChain.realize hκ hs h00 hreal z hz.2.2.1 P LP
  have hR := H.rightChain.realize hκ hs h00 hreal z hz.2.2.2.1 Q RP
  have e := H.comparison.realizeBetween H.leftObject H.rightObject z hz.2.2.2.2.1
    hz.2.2.2.2.2.1 hz.2.2.2.2.2.2 LP RP
  exact ⟨H.leftLength,H.rightLength,gammaUniversalObject LP.toGamma,gammaUniversalObject RP.toGamma,
    hL,hR,gammaUniversalIso LP.toGamma RP.toGamma e⟩

theorem GammaFiniteCommonSchema.realize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteCommonSchema U V)
    (z : Fin p → M) (hz : H.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (U.rowDomain z) (U.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (V.rowDomain z) (V.rowVolume z)) :
    GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma :=
  ⟨Set.univ,Set.subset_univ _,Set.subset_univ _,H.realizeAt hκ hs h00 hreal z hz P Q⟩

end IntegrationInACVF.Section6
