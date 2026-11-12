import IntegrationSection6.GammaRecodingAgreements
import IntegrationSection6.GammaSchemaValidityTransport
import IntegrationSection6.GammaRowOperationAgreement

/-! Primitive formula-row agreement transports validity of entire finite
blowup witnesses and exact-length chains to new sorted parameter tuples.
The proof uses the actual elementary/coproduct row identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaParameterRecode.object_valid (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ j, sortEval (sq j) (t j)) (hRows : C.ObjectAgreement F z t) (hF : F.valid z) :
    (C.object F).valid t :=
  F.valid_of_rowAgreement (C.object F) z t ht rfl hRows hF

theorem GammaParameterRecode.iso_valid (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVIsoSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ j, sortEval (sq j) (t j)) (hRows : C.IsoAgreement F z t) (hF : F.valid z) :
    (C.iso F).valid t :=
  F.valid_of_rowAgreement (C.iso F) z t ht rfl rfl hRows.1 hRows.2.1 hRows.2.2 hF

variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}

theorem GammaParameterRecode.blowup_valid (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteBlowupSchema U V) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ j, sortEval (sp j) (z j)) (ht : ∀ j, sortEval (sq j) (t j))
    (hU : C.ObjectAgreement U z t) (hV : C.ObjectAgreement V z t)
    (hRows : C.BlowupAgreement H z t) (hH : H.valid z) : (C.blowup H).valid t := by
  have hC := hRows.1
  have hR := hRows.2.1
  have hS := hRows.2.2.1
  have hT := hRows.2.2.2
  refine ⟨?_,C.object_valid H.remainder z t ht hR hH.2.1,
    C.iso_valid H.sourceChart z t ht hS hH.2.2.1,
    C.iso_valid H.resultChart z t ht hT hH.2.2.2.1,?_,?_,?_,?_⟩
  · exact H.admissibility.valid_of_rowAgreement (C.blowup H).admissibility z t ht rfl rfl rfl hC hH.1
  · exact gammaSchemaSameRow_of_agreement ht hS.1 hU hH.2.2.2.2.1
  · exact gammaSchemaSameRow_of_agreement ht hS.2.1 (hC.coprod hR hz ht) hH.2.2.2.2.2.1
  · exact gammaSchemaSameRow_of_agreement ht hT.1 hV hH.2.2.2.2.2.2.1
  · exact gammaSchemaSameRow_of_agreement ht hT.2.1
      ((hC.elementary hz ht H.coordinate).coprod hR hz ht) hH.2.2.2.2.2.2.2

theorem GammaParameterRecode.chain_valid (C : GammaParameterRecode B p q sp sq)
    {r : ℕ} (H : GammaFiniteChainSchema U V r) :
    ∀ (z : Fin p → M) (t : Fin q → M),
      (∀ j, sortEval (sp j) (z j)) → (∀ j, sortEval (sq j) (t j)) →
      C.ObjectAgreement U z t → C.ObjectAgreement V z t → C.ChainAgreement H z t →
      H.valid z → (C.chain H).valid t := by
  induction H with
  | iso chart =>
    intro z t hz ht hU hV hRows hH
    exact ⟨C.iso_valid chart z t ht hRows hH.1,
      gammaSchemaSameRow_of_agreement ht hRows.1 hU hH.2.1,
      gammaSchemaSameRow_of_agreement ht hRows.2.1 hV hH.2.2⟩
  | step W head tail ih =>
    intro z t hz ht hU hV hRows hH
    exact ⟨C.object_valid W z t ht hRows.1 hH.1,
      C.blowup_valid head z t hz ht hU hRows.1 hRows.2.1 hH.2.1,
      ih z t hz ht hRows.1 hV hRows.2.2 hH.2.2⟩

theorem GammaParameterRecode.common_valid (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteCommonSchema U V) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ j, sortEval (sp j) (z j)) (ht : ∀ j, sortEval (sq j) (t j))
    (hU : C.ObjectAgreement U z t) (hV : C.ObjectAgreement V z t)
    (hRows : C.CommonAgreement H z t) (hH : H.valid z) : (C.common H).valid t :=
  ⟨C.object_valid H.leftObject z t ht hRows.1 hH.1,
    C.object_valid H.rightObject z t ht hRows.2.1 hH.2.1,
    C.chain_valid H.leftChain z t hz ht hU hRows.1 hRows.2.2.1 hH.2.2.1,
    C.chain_valid H.rightChain z t hz ht hV hRows.2.1 hRows.2.2.2.1 hH.2.2.2.1,
    C.iso_valid H.comparison z t ht hRows.2.2.2.2 hH.2.2.2.2.1,
    gammaSchemaSameRow_of_agreement ht hRows.2.2.2.2.1 hRows.1 hH.2.2.2.2.2.1,
    gammaSchemaSameRow_of_agreement ht hRows.2.2.2.2.2.1 hRows.2.1 hH.2.2.2.2.2.2⟩

end IntegrationInACVF.Section6
