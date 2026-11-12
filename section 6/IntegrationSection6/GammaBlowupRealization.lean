import IntegrationSection6.GammaSchemaUniversalGeometry

/-! Every valid blowup schema row realizes an actual geometric finite
blowup at a common internal code presentation. No definability of the
common-blowup relation is assumed. -/
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

theorem GammaFiniteBlowupSchema.realizeBlowup {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteBlowupSchema U V)
    (z : Fin p → M) (hz : H.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (U.rowDomain z) (U.rowVolume z))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k
      (V.rowDomain z) (V.rowVolume z)) :
    Nonempty (GammaBlowupAt hκ hs h00 (small_union_range hκ B.real hreal z)
      (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma)) := by
  obtain ⟨CP,RP,hSource,hResult⟩ := H.realize hκ hs h00 hreal z hz P Q
  let hParam := hz.1.1.1
  let hAd := H.admissibility.admissible z hz.1 CP
  let EP := H.center.elementaryPresentation hκ hs h00 hreal z hParam CP H.coordinate hAd
  let hC := H.center.valid_row_support hz.1.1
  let hR := H.remainder.valid_row_support hz.2.1
  let hE := H.center.elementary_row_support H.coordinate z hParam
  let SP := H.center.coprodPresentation H.remainder z hParam hC hR CP RP
  let TP := (H.center.elementaryFormula H.coordinate).coprodPresentation H.remainder z hParam hE hR EP RP
  obtain ⟨es⟩ := gammaUniversalIso P.toGamma SP.toGamma (Classical.choice hSource)
  obtain ⟨et⟩ := gammaUniversalIso Q.toGamma TP.toGamma (Classical.choice hResult)
  have hsEq : gammaUniversalObject SP.toGamma =
      gammaCoprodAt (gammaUniversalObject CP.toGamma) (gammaUniversalObject RP.toGamma) :=
    H.center.universal_coprodPresentation H.remainder z hParam hC hR CP RP
  have htEq : gammaUniversalObject TP.toGamma =
      gammaCoprodAt (gammaUniversalObject EP.toGamma) (gammaUniversalObject RP.toGamma) :=
    (H.center.elementaryFormula H.coordinate).universal_coprodPresentation H.remainder z hParam hE hR EP RP
  have heEq := H.center.universal_elementaryPresentation hκ hs h00 hreal z hParam CP H.coordinate hAd
  rw [hsEq] at es
  rw [htEq,heEq] at et
  exact ⟨{
    center := gammaUniversalObject CP.toGamma
    remainder := gammaUniversalObject RP.toGamma
    coordinate := H.coordinate
    admissible := gammaUniversalObject_admissible CP.toGamma hAd
    source := es
    result := et }⟩

end IntegrationInACVF.Section6
