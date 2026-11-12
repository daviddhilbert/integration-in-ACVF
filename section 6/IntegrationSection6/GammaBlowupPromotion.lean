import IntegrationSection6.GammaBlowupSchemata
import IntegrationSection6.GammaSchemaElementaryRepresentation
import IntegrationSection6.GammaSchemaCoproductRepresentation
import IntegrationSection6.GammaAdmissibilityPromotion
import IntegrationSection6.GammaIsomorphismPromotion
import IntegrationSection6.FiniteGammaBlowups

/-! Every actual finite original-Gamma blowup over a named sorted tuple
has a finite formula witness whose genuine validity locus contains that
tuple. Only original real/Gamma names enter the saturation bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p k : ℕ}

theorem gamma_sorted_finite_blowup_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    {hsmall : Cardinal.mk ↥(B.real ∪ Set.range z) < κ}
    (U V : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ S k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k sp)
    (G : GammaFiniteRVSchema B p (rvObjectArity V.object.obj) k sp)
    (hF : gammaSchemaRepresents U.toGamma F z) (hG : gammaSchemaRepresents V.toGamma G z)
    (H : FiniteRV.GammaBlowupAt hκ hs h00 hsmall U V) :
    ∃ W : GammaFiniteBlowupSchema F G, W.valid z := by
  obtain ⟨A,hAi,hA,hCD,hCV⟩ := gamma_sorted_finite_admissibility_promotion
    hκ hs h00 hreal hgamma sp z hz H.center.toGamma H.coordinate H.admissible
  obtain ⟨R,hR,hRD,hRV⟩ := gamma_sorted_finite_object_promotion
    hκ hs hreal hgamma sp z hz H.remainder.toGamma
  obtain ⟨I,hI,hID,hIV,hITD,hITV,_⟩ := gamma_sorted_finite_isomorphism_promotion
    hκ hs hreal hgamma sp z hz U.toGamma (FiniteRV.gammaCoprodAt H.center H.remainder).toGamma H.source.toGamma
  obtain ⟨J,hJ,hJD,hJV,hJTD,hJTV,_⟩ := gamma_sorted_finite_isomorphism_promotion
    hκ hs hreal hgamma sp z hz V.toGamma
      (FiniteRV.gammaCoprodAt (FiniteRV.gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible) H.remainder).toGamma
      H.result.toGamma
  have hC : gammaSchemaRepresents H.center.toGamma A.object z := ⟨hCD,hCV⟩
  have hRest : gammaSchemaRepresents H.remainder.toGamma R z := ⟨hRD,hRV⟩
  have hSum := gammaSchemaRepresents_coprod H.center H.remainder A.object R z hz hC hRest
  have hE : gammaSchemaRepresents
      (FiniteRV.gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible).toGamma
      (A.object.elementaryFormula A.coordinate) z := by
    rw [hAi]
    exact gammaSchemaRepresents_elementary hκ hs h00 hsmall H.center.toGamma A.object z hz hC H.coordinate H.admissible
  have hTargetSum := gammaSchemaRepresents_coprod
    (FiniteRV.gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible) H.remainder
    (A.object.elementaryFormula A.coordinate) R z hz hE hRest
  let W : GammaFiniteBlowupSchema F G := {
    centerArity := rvObjectArity H.center.object.obj
    remainderArity := rvObjectArity H.remainder.object.obj
    center := A.object
    remainder := R
    coordinate := A.coordinate
    admissibilityBound := A.bound
    sourceChart := I
    resultChart := J }
  refine ⟨W,hA,hR,hI,hJ,?_,?_,?_,?_⟩
  · exact gammaSchemaRepresents_sameRow U.toGamma I.source F z hz ⟨hID,hIV⟩ hF
  · exact gammaSchemaRepresents_sameRow (FiniteRV.gammaCoprodAt H.center H.remainder).toGamma
      I.target (A.object.coprodFormula R) z hz ⟨hITD,hITV⟩ hSum
  · exact gammaSchemaRepresents_sameRow V.toGamma J.source G z hz ⟨hJD,hJV⟩ hG
  · exact gammaSchemaRepresents_sameRow
      (FiniteRV.gammaCoprodAt (FiniteRV.gammaElementaryAt hκ hs h00 hsmall H.center H.coordinate H.admissible) H.remainder).toGamma
      J.target ((A.object.elementaryFormula A.coordinate).coprodFormula R) z hz ⟨hJTD,hJTV⟩ hTargetSum

end IntegrationInACVF.Section6
