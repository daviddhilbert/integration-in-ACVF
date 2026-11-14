import Integration7.GammaVolumeWitnessRecoding

/-! Primitive-row agreement transports validity of complete volume
blowups, chains and common witnesses to the recoded parameter block. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k r : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeParameterRecode.BlowupAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (h : H.NoAuxiliary) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.center z t ∧ C.VolumeObjectAgreement H.remainder z t ∧
    C.CertificateAgreement H.sourceChart h.1 z t ∧ C.CertificateAgreement H.resultChart h.2 z t

def GammaVolumeParameterRecode.ChainAgreement (C : GammaVolumeParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaRVVolumeSchema B p a k sp} → {G : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → (H : GammaVolumeChainSchema F G r) → H.NoAuxiliary → (Fin p → M) → (Fin q → M) → Prop
  | _,_,_,_,_,.iso chart,h,z,t => C.CertificateAgreement chart h z t
  | _,_,_,_,_,.step W head tail,h,z,t =>
      C.VolumeObjectAgreement W z t ∧ C.BlowupAgreement head h.1 z t ∧ C.ChainAgreement tail h.2 z t

def GammaVolumeParameterRecode.CommonAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (h : H.NoAuxiliary) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.leftObject z t ∧ C.VolumeObjectAgreement H.rightObject z t ∧
    C.ChainAgreement H.leftChain h.1 z t ∧ C.ChainAgreement H.rightChain h.2.1 z t ∧
      C.CertificateAgreement H.comparison h.2.2 z t

theorem GammaVolumeParameterRecode.blowup_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (hAux : H.NoAuxiliary) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hU : C.VolumeObjectAgreement F z t) (hV : C.VolumeObjectAgreement G z t)
    (h : C.BlowupAgreement H hAux z t) (hValid : H.valid z) : (C.blowup H hAux).valid t := by
  rcases hValid with ⟨hF,hG,hA,hR,hAd,hS,hT,hSF,hSA,hTG,hTA⟩
  have hAR := C.volumeObject_rows H.center z t h.1
  have hRR := C.volumeObject_rows H.remainder z t h.2.1
  have hSR := h.2.2.1
  have hTR := h.2.2.2
  refine ⟨C.volumeObject_valid F z t ht hU hF,C.volumeObject_valid G z t ht hV hG,
    C.volumeObject_valid H.center z t ht h.1 hA,C.volumeObject_valid H.remainder z t ht h.2.1 hR,
    ?_,C.certificate_valid H.sourceChart hAux.1 z t ht hSR hS,
    C.certificate_valid H.resultChart hAux.2 z t ht hTR hT,?_,?_,?_,?_⟩
  · exact H.admissibility.valid_of_rowAgreement (C.blowup H hAux).admissibility z t ht rfl rfl rfl hAR.1 hAd
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hSR.1)
      (C.volumeObject_rows _ z t hU) hSF
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hSR.2.1)
      (hAR.coprod hRR hz ht) hSA
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hTR.1)
      (C.volumeObject_rows _ z t hV) hTG
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hTR.2.1)
      ((hAR.elementary hz ht).coprod hRR hz ht) hTA

theorem GammaVolumeParameterRecode.chain_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeChainSchema F G r) :
    ∀ (hAux : H.NoAuxiliary) (z : Fin p → M) (t : Fin q → M),
      (∀ i, sortEval (sp i) (z i)) → (∀ i, sortEval (sq i) (t i)) →
      C.VolumeObjectAgreement F z t → C.VolumeObjectAgreement G z t →
      C.ChainAgreement H hAux z t → H.valid z → (C.chain H hAux).valid t := by
  induction H with
  | iso chart =>
    intro hAux z t hz ht hU hV h hValid
    exact ⟨C.certificate_valid chart hAux z t ht h hValid.1,
      gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.1)
        (C.volumeObject_rows _ z t hU) hValid.2.1,
      gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.1)
        (C.volumeObject_rows _ z t hV) hValid.2.2⟩
  | step W head tail ih =>
    intro hAux z t hz ht hU hV h hValid
    exact ⟨C.volumeObject_valid W z t ht h.1 hValid.1,
      C.blowup_valid head hAux.1 z t hz ht hU h.1 h.2.1 hValid.2.1,
      ih hAux.2 z t hz ht h.1 hV h.2.2 hValid.2.2⟩

theorem GammaVolumeParameterRecode.common_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (hAux : H.NoAuxiliary) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hU : C.VolumeObjectAgreement F z t) (hV : C.VolumeObjectAgreement G z t)
    (h : C.CommonAgreement H hAux z t) (hValid : H.valid z) : (C.common H hAux).valid t := by
  rcases hValid with ⟨hF,hG,hL,hR,hlc,hrc,hCmp,hCmpL,hCmpR⟩
  exact ⟨C.volumeObject_valid F z t ht hU hF,C.volumeObject_valid G z t ht hV hG,
    C.volumeObject_valid H.leftObject z t ht h.1 hL,C.volumeObject_valid H.rightObject z t ht h.2.1 hR,
    C.chain_valid H.leftChain hAux.1 z t hz ht hU h.1 h.2.2.1 hlc,
    C.chain_valid H.rightChain hAux.2.1 z t hz ht hV h.2.1 h.2.2.2.1 hrc,
    C.certificate_valid H.comparison hAux.2.2 z t ht h.2.2.2.2 hCmp,
    gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.2.2.2.1)
      (C.volumeObject_rows _ z t h.1) hCmpL,
    gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.2.2.2.2.1)
      (C.volumeObject_rows _ z t h.2.1) hCmpR⟩

end IntegrationInACVF.Section7
