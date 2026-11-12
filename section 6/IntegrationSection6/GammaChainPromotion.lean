import IntegrationSection6.GammaChainSchemata
import IntegrationSection6.GammaBlowupPromotion
import IntegrationSection6.FiniteGammaIterations

/-! Actual finite forward Gamma blowup chains promote to finite formula
witnesses of the same length, over arbitrary sorted parameter tuples.
Every intermediate object is promoted with its finite volume bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p k : ℕ}

theorem gamma_sorted_finite_chain_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    {hsmall : Cardinal.mk ↥(B.real ∪ Set.range z) < κ}
    {U V : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ S k} {r : ℕ}
    (H : FiniteRV.GammaIteratedBlowup hκ hs h00 hsmall r U V) :
    ∀ (F : GammaFiniteRVSchema B p (rvObjectArity U.object.obj) k sp)
      (G : GammaFiniteRVSchema B p (rvObjectArity V.object.obj) k sp),
      gammaSchemaRepresents U.toGamma F z → gammaSchemaRepresents V.toGamma G z →
      ∃ W : GammaFiniteChainSchema F G r, W.valid z := by
  induction H with
  | @zero U V he =>
    intro F G hF hG
    obtain ⟨e⟩ := he
    obtain ⟨I,hI,hID,hIV,hITD,hITV,_⟩ := gamma_sorted_finite_isomorphism_promotion
      hκ hs hreal hgamma sp z hz U.toGamma V.toGamma e.toGamma
    refine ⟨.iso I,hI,?_,?_⟩
    · exact gammaSchemaRepresents_sameRow U.toGamma I.source F z hz ⟨hID,hIV⟩ hF
    · exact gammaSchemaRepresents_sameRow V.toGamma I.target G z hz ⟨hITD,hITV⟩ hG
  | @cons r U V W he htail ih =>
    intro F G hF hG
    obtain ⟨T,hT,hTD,hTV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz V.toGamma
    have hRep : gammaSchemaRepresents V.toGamma T z := ⟨hTD,hTV⟩
    obtain ⟨head,hHead⟩ := gamma_sorted_finite_blowup_promotion hκ hs h00 hreal hgamma sp z hz
      U V F T hF hRep (Classical.choice he)
    obtain ⟨tail,hTail⟩ := ih T G hRep hG
    exact ⟨.step T head tail,hT,hHead,hTail⟩

end IntegrationInACVF.Section6
