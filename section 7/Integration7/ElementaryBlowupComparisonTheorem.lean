import Integration7.ElementaryBlowupIsomorphism

/-! Lemma 7.2 of arXiv:0809.0473v2. The numbered statement was compared
with Section 7 of the paper; positive degree is written k+1 since there
are no elementary blowups in ordinary RV[0]. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem lemma_7_2
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV)
    (h : Nonempty (RVVolumeIso U V)) : Nonempty (RVVolumeIso WU WV) := by
  obtain ⟨f⟩ := h
  exact ⟨elementaryBlowupIso hc C f b c⟩

end IntegrationInACVF.Section7
