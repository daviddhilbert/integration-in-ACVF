import Integration7.IndexedVolumeChartTransfer
import Integration7.IndexedVolumeCoproductRealization
import Integration7.IndexedVolumeElementaryRealization
import Integration7.IndexedVolumeEqualRowPresentations
import Integration7.VolumeExtensionCoherence

/-! A uniformly valid volume-blowup witness assembles to a genuine
forward volume blowup over an arbitrary finite-volume RV index base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
variable {G : GammaRVVolumeSchema B p b k (fun _ => .rv)}

theorem GammaRVVolumeBlowupSchema.indexedRealize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeBlowupSchema F G)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      Nonempty (VolumeBlowup ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD)) := by
  have hA : ∀ t ∈ T, H.center.valid (rvValues t) := fun t ht => (hvalid t ht).2.2.1
  have hR : ∀ t ∈ T, H.remainder.valid (rvValues t) := fun t ht => (hvalid t ht).2.2.2.1
  have hAd : ∀ t ∈ T, H.admissibility.valid (rvValues t) := fun t ht => (hvalid t ht).2.2.2.2.1
  have hS : ∀ t ∈ T, H.sourceChart.valid (rvValues t) := fun t ht => (hvalid t ht).2.2.2.2.2.1
  have hT : ∀ t ∈ T, H.resultChart.valid (rvValues t) := fun t ht => (hvalid t ht).2.2.2.2.2.2.1
  have hSF : ∀ t ∈ T, H.sourceChart.source.sameRow F (rvValues t) :=
    fun t ht => (hvalid t ht).2.2.2.2.2.2.2.1
  have hSA : ∀ t ∈ T, H.sourceChart.target.sameRow (H.center.coprodFormula H.remainder) (rvValues t) :=
    fun t ht => (hvalid t ht).2.2.2.2.2.2.2.2.1
  have hTG : ∀ t ∈ T, H.resultChart.source.sameRow G (rvValues t) :=
    fun t ht => (hvalid t ht).2.2.2.2.2.2.2.2.2.1
  have hTA : ∀ t ∈ T, H.resultChart.target.sameRow
      (H.center.elementaryFormula.coprodFormula H.remainder) (rvValues t) :=
    fun t ht => (hvalid t ht).2.2.2.2.2.2.2.2.2.2
  have hAF : ∀ t ∈ T, H.center.object.finiteRow (rvValues t) :=
    fun t ht => H.center.object.finiteRow_of_valid _ (hA t ht).1
  have hRF : ∀ t ∈ T, H.remainder.object.finiteRow (rvValues t) :=
    fun t ht => H.remainder.object.finiteRow_of_valid _ (hR t ht).1
  have hEF : ∀ t ∈ T, H.center.elementaryFormula.object.finiteRow (rvValues t) :=
    fun t ht => H.admissibility.elementary_finiteRow C.uncountable.le C.saturated C.model00
      ((Cardinal.mk_le_mk_of_subset hB).trans_lt C.small) _ (hAd t ht)
  let AP := H.center.indexedVolumePresentation BP hA
  let RP := H.remainder.indexedVolumePresentation BP hR
  let EP := H.center.indexedElementaryPresentation C BP H.admissibilityBound hA hAd hB
  let SP := H.sourceChart.target.indexedPresentation_of_sameRow
    (H.center.coprodFormula H.remainder) BP (fun t ht => (hS t ht).2.1) hSA
  let TP := H.resultChart.target.indexedPresentation_of_sameRow
    (H.center.elementaryFormula.coprodFormula H.remainder) BP (fun t ht => (hT t ht).2.1) hTA
  obtain ⟨C₁,hCC₁,hAP₁⟩ := AP.exists_containingContext C hB
  obtain ⟨C₂,hC₁C₂,hRP₂⟩ := RP.exists_containingContext C₁ (hB.trans hCC₁)
  obtain ⟨C₃,hC₂C₃,hEP₃⟩ := EP.exists_containingContext C₂ (hB.trans (hCC₁.trans hC₁C₂))
  obtain ⟨C₄,hC₃C₄,hSP₄⟩ := SP.exists_containingContext C₃ (hB.trans (hCC₁.trans (hC₁C₂.trans hC₂C₃)))
  obtain ⟨C₀,hC₄C₀,hTP⟩ := TP.exists_containingContext C₄
    (hB.trans (hCC₁.trans (hC₁C₂.trans (hC₂C₃.trans hC₃C₄))))
  let hCC₀ := hCC₁.trans (hC₁C₂.trans (hC₂C₃.trans (hC₃C₄.trans hC₄C₀)))
  let hAP := hAP₁.trans (hC₁C₂.trans (hC₂C₃.trans (hC₃C₄.trans hC₄C₀)))
  let hRP := hRP₂.trans (hC₂C₃.trans (hC₃C₄.trans hC₄C₀))
  let hEP := hEP₃.trans (hC₃C₄.trans hC₄C₀)
  let hSP := hSP₄.trans hC₄C₀
  obtain ⟨D₁,hC₀D₁,⟨eS₀⟩⟩ := H.sourceChart.indexedRealizeBetween hc C₀ F
    (H.center.coprodFormula H.remainder) BP hS hSF hSA P SP (hP.trans hCC₀) hSP
    (hBP.trans hCC₀) (hB.trans hCC₀)
  obtain ⟨D₂,hD₁D₂,⟨eS₁⟩⟩ := H.center.indexedCoprodRealize hc D₁ H.remainder BP hAF hRF AP RP SP
    (hAP.trans hC₀D₁) (hRP.trans hC₀D₁) (hSP.trans hC₀D₁) (hB.trans (hCC₀.trans hC₀D₁))
  let hC₀D₂ := hC₀D₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,⟨eT₀⟩⟩ := H.resultChart.indexedRealizeBetween hc D₂ G
    (H.center.elementaryFormula.coprodFormula H.remainder) BP hT hTG hTA Q TP
    (hQ.trans (hCC₀.trans hC₀D₂)) (hTP.trans hC₀D₂)
    (hBP.trans (hCC₀.trans hC₀D₂)) (hB.trans (hCC₀.trans hC₀D₂))
  let hC₀D₃ := hC₀D₂.trans hD₂D₃
  obtain ⟨D₄,hD₃D₄,⟨eT₁⟩⟩ := H.center.elementaryFormula.indexedCoprodRealize hc D₃ H.remainder BP
    hEF hRF EP RP TP (hEP.trans hC₀D₃) (hRP.trans hC₀D₃) (hTP.trans hC₀D₃)
    (hB.trans (hCC₀.trans hC₀D₃))
  let hC₀D₄ := hC₀D₃.trans hD₃D₄
  let hAP₄ := hAP.trans hC₀D₄
  let hRP₄ := hRP.trans hC₀D₄
  have hAdm := H.center.indexed_admissible hc D₄ BP H.admissibilityBound hAd AP hAP₄
  obtain ⟨D₅,hD₄D₅,⟨eE⟩⟩ := H.center.indexedElementaryRealize hc D₄ BP hA hEF AP EP hAP₄
    (hEP.trans hC₀D₄) hAdm (hB.trans (hCC₀.trans hC₀D₄))
  let hD₂D₅ := hD₂D₃.trans (hD₃D₄.trans hD₄D₅)
  let hD₃D₅ := hD₃D₄.trans hD₄D₅
  let L := (AP.inContext hc D₄ hAP₄).toObject
  let R := (RP.inContext hc D₄ hRP₄).toObject
  refine ⟨D₅,hCC₀.trans (hC₀D₄.trans hD₄D₅),⟨{
    locus := L.extend hD₄D₅
    complement := R.extend hD₄D₅
    blownLocus := (elementaryVolumeObject D₄ L hAdm).extend hD₄D₅
    elementary := (elementaryVolumeBlowup D₄ L hAdm).extend hD₄D₅
    sourceIso := (eS₀.extend (hD₁D₂.trans hD₂D₅)).trans hc D₅ (eS₁.extend hD₂D₅)
    targetIso := ((eT₀.extend hD₃D₅).trans hc D₅ (eT₁.extend hD₄D₅)).trans hc D₅
      (eE.coprod hc D₅ (RVVolumeIso.refl hc D₅ (R.extend hD₄D₅))) }⟩⟩

end IntegrationInACVF.Section7
