import IntegrationSection6.GammaSchemaIndexedChartTransfer
import IntegrationSection6.GammaSchemaIndexedCoproductTransfer
import IntegrationSection6.GammaSchemaIndexedElementaryIso
import IntegrationSection6.GammaSchemaUniversalGeometry
import IntegrationSection6.FiniteGammaCoproductMaps

/-! A single uniformly valid finite blowup witness glues over an actual
RV[d] base to a native blowup in RV[d+k]. The index set may be infinite.
Every splitting chart retains its full original-base Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaFiniteRVSchema B p a k (fun _ => .rv)} {G : GammaFiniteRVSchema B p b k (fun _ => .rv)}
open FiniteRV

theorem GammaFiniteBlowupSchema.indexedRealize {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (H : GammaFiniteBlowupSchema F G)
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (fun j => (t j).val))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    Nonempty (GammaBlowupAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma)) := by
  let hA := fun t ht => (hvalid t ht).1
  let hC := fun t ht => (hvalid t ht).1.1
  let hR := fun t ht => (hvalid t ht).2.1
  let hCFin := fun t ht => H.center.finiteRow_of_valid _ (hC t ht)
  let hRFin := fun t ht => H.remainder.finiteRow_of_valid _ (hR t ht)
  let hEFin := fun t ht => H.admissibility.elementary_finiteRow hκ hs h00 hreal _ (hA t ht)
  let CP := H.center.indexedPresentation BP hC
  let RP := H.remainder.indexedPresentation BP hR
  let EP := (H.center.elementaryFormula H.coordinate).indexedPresentation_finiteRows BP hEFin
  let SC := (H.center.coprodFormula H.remainder).indexedPresentation_finiteRows BP
    (fun t ht => H.center.finiteRow_coprod H.remainder _ (fun j => (t j).property) (hCFin t ht) (hRFin t ht))
  let TC := ((H.center.elementaryFormula H.coordinate).coprodFormula H.remainder).indexedPresentation_finiteRows BP
    (fun t ht => (H.center.elementaryFormula H.coordinate).finiteRow_coprod H.remainder _
      (fun j => (t j).property) (hEFin t ht) (hRFin t ht))
  let eS0 := H.sourceChart.indexedIsoBetween F (H.center.coprodFormula H.remainder) BP
    (fun t ht => (hvalid t ht).2.2.1)
    (fun t ht => (hvalid t ht).2.2.2.2.1) (fun t ht => (hvalid t ht).2.2.2.2.2.1) P SC
  let eS1 := H.center.indexedCoprodIsoFromRows H.remainder BP hCFin hRFin CP RP SC
  let eS := gammaFiniteIsoTrans P.toGamma SC.toGamma (CP.coprod RP).toGamma eS0 eS1
  let eT0 := H.resultChart.indexedIsoBetween G ((H.center.elementaryFormula H.coordinate).coprodFormula H.remainder) BP
    (fun t ht => (hvalid t ht).2.2.2.1)
    (fun t ht => (hvalid t ht).2.2.2.2.2.2.1) (fun t ht => (hvalid t ht).2.2.2.2.2.2.2) Q TC
  let eT1 := (H.center.elementaryFormula H.coordinate).indexedCoprodIsoFromRows H.remainder BP hEFin hRFin EP RP TC
  let eT := gammaFiniteIsoTrans Q.toGamma TC.toGamma (EP.coprod RP).toGamma eT0 eT1
  let hAd := H.admissibility.indexed_admissible BP hA CP
  let eE := H.admissibility.indexedElementaryIso hκ hs h00 hreal BP hA CP EP
  obtain ⟨es⟩ := gammaUniversalIso P.toGamma (CP.coprod RP).toGamma eS
  obtain ⟨et⟩ := gammaUniversalIso Q.toGamma (EP.coprod RP).toGamma eT
  obtain ⟨ee⟩ := gammaUniversalIso EP.toGamma
    (gammaFiniteElementaryBasic hκ hs h00 hreal CP.toGamma (Fin.natAdd d H.coordinate) hAd) eE
  have hsEq : gammaUniversalObject (CP.coprod RP).toGamma =
      gammaCoprodAt (gammaUniversalObject CP.toGamma) (gammaUniversalObject RP.toGamma) :=
    gammaUniversalObject_graphCoprod CP RP
  have htEq : gammaUniversalObject (EP.coprod RP).toGamma =
      gammaCoprodAt (gammaUniversalObject EP.toGamma) (gammaUniversalObject RP.toGamma) :=
    gammaUniversalObject_graphCoprod EP RP
  rw [hsEq] at es
  rw [htEq] at et
  rw [gammaUniversalObject_elementary hκ hs h00 hreal CP.toGamma (Fin.natAdd d H.coordinate) hAd] at ee
  exact ⟨{
    center := gammaUniversalObject CP.toGamma
    remainder := gammaUniversalObject RP.toGamma
    coordinate := Fin.natAdd d H.coordinate
    admissible := gammaUniversalObject_admissible CP.toGamma hAd
    source := es
    result := et.trans (gammaCoprodIsoAt ee (GammaIsoAt.refl (gammaUniversalObject RP.toGamma))) }⟩

end IntegrationInACVF.Section6
