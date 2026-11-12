import IntegrationSection6.GammaCommonBlowupSchemata
import IntegrationSection6.GammaChainPromotion
import IntegrationSection6.FiniteGammaCommonBlowups

/-! Promote actual common forward blowups to finite formula witnesses.
Arbitrary internal code presentations remain internal throughout. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p k : ℕ}

theorem gamma_sorted_finite_common_promotion_at {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    {hsmall : Cardinal.mk ↥(B.real ∪ Set.range z) < κ}
    (U V : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ S k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k sp)
    (G : GammaFiniteRVSchema B p (rvObjectArity V.object.obj) k sp)
    (hF : gammaSchemaRepresents U.toGamma F z) (hG : gammaSchemaRepresents V.toGamma G z)
    (H : FiniteRV.GammaIspAt hκ hs h00 hsmall U V) :
    ∃ W : GammaFiniteCommonSchema F G, W.valid z := by
  obtain ⟨r,s,A,C,hU,hV,⟨e⟩⟩ := H
  obtain ⟨L,hL,hLD,hLV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz A.toGamma
  obtain ⟨R,hR,hRD,hRV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz C.toGamma
  have hRepL : gammaSchemaRepresents A.toGamma L z := ⟨hLD,hLV⟩
  have hRepR : gammaSchemaRepresents C.toGamma R z := ⟨hRD,hRV⟩
  obtain ⟨LC,hLC⟩ := gamma_sorted_finite_chain_promotion hκ hs h00 hreal hgamma sp z hz hU F L hF hRepL
  obtain ⟨RC,hRC⟩ := gamma_sorted_finite_chain_promotion hκ hs h00 hreal hgamma sp z hz hV G R hG hRepR
  obtain ⟨I,hI,hID,hIV,hITD,hITV,_⟩ := gamma_sorted_finite_isomorphism_promotion
    hκ hs hreal hgamma sp z hz A.toGamma C.toGamma e.toGamma
  let W : GammaFiniteCommonSchema F G := {
    leftArity := rvObjectArity A.object.obj
    rightArity := rvObjectArity C.object.obj
    leftObject := L
    rightObject := R
    leftLength := r
    rightLength := s
    leftChain := LC
    rightChain := RC
    comparison := I }
  exact ⟨W,hL,hR,hLC,hRC,hI,
    gammaSchemaRepresents_sameRow A.toGamma I.source L z hz ⟨hID,hIV⟩ hRepL,
    gammaSchemaRepresents_sameRow C.toGamma I.target R z hz ⟨hITD,hITV⟩ hRepR⟩

theorem gamma_sorted_finite_common_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    {hsmall : Cardinal.mk ↥(B.real ∪ Set.range z) < κ}
    (U V : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp)
    (G : GammaFiniteRVSchema B p (rvObjectArity V.object) k sp)
    (hF : gammaSchemaRepresents U F z) (hG : gammaSchemaRepresents V G z)
    (H : FiniteRV.GammaIsp hκ hs h00 hsmall U V) :
    ∃ W : GammaFiniteCommonSchema F G, W.valid z := by
  obtain ⟨S,hUS,hVS,hI⟩ := H
  exact gamma_sorted_finite_common_promotion_at hκ hs h00 hreal hgamma sp z hz
    (FiniteRV.gammaObjectAtExtend U hUS) (FiniteRV.gammaObjectAtExtend V hVS) F G
    ⟨hF.1,hF.2⟩ ⟨hG.1,hG.2⟩ hI

end IntegrationInACVF.Section6
