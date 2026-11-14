import Integration7.FrozenVolumeCertificateRecoding
import Integration7.GammaVolumeWitnessValidity

/-! General common-witness recoding. Old parameter tuples remain inside
existential exception certificates; full geometric rows and exact chain
lengths are retained without an auxiliary-free hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k r : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeParameterRecode.blowupWithFrozenParameters (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) : GammaRVVolumeBlowupSchema (C.volumeObject F) (C.volumeObject G) where
  centerArity := H.centerArity
  remainderArity := H.remainderArity
  center := C.volumeObject H.center
  remainder := C.volumeObject H.remainder
  admissibilityBound := H.admissibilityBound
  sourceChart := C.certificateWithFrozenParameters H.sourceChart
  resultChart := C.certificateWithFrozenParameters H.resultChart

def GammaVolumeParameterRecode.chainWithFrozenParameters (C : GammaVolumeParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaRVVolumeSchema B p a k sp} → {G : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → GammaVolumeChainSchema F G r → GammaVolumeChainSchema (C.volumeObject F) (C.volumeObject G) r
  | _,_,_,_,_,.iso chart => .iso (C.certificateWithFrozenParameters chart)
  | _,_,_,_,_,.step W head tail =>
      .step (C.volumeObject W) (C.blowupWithFrozenParameters head) (C.chainWithFrozenParameters tail)

def GammaVolumeParameterRecode.commonWithFrozenParameters (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) : GammaVolumeCommonSchema (C.volumeObject F) (C.volumeObject G) where
  leftArity := H.leftArity
  rightArity := H.rightArity
  leftObject := C.volumeObject H.leftObject
  rightObject := C.volumeObject H.rightObject
  leftLength := H.leftLength
  rightLength := H.rightLength
  leftChain := C.chainWithFrozenParameters H.leftChain
  rightChain := C.chainWithFrozenParameters H.rightChain
  comparison := C.certificateWithFrozenParameters H.comparison

def GammaVolumeParameterRecode.BlowupGeometryAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.center z t ∧ C.VolumeObjectAgreement H.remainder z t ∧
    C.CertificateGeometryAgreement H.sourceChart z t ∧ C.CertificateGeometryAgreement H.resultChart z t

def GammaVolumeParameterRecode.ChainGeometryAgreement (C : GammaVolumeParameterRecode B p q sp sq) :
    {a b : ℕ} → {F : GammaRVVolumeSchema B p a k sp} → {G : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → GammaVolumeChainSchema F G r → (Fin p → M) → (Fin q → M) → Prop
  | _,_,_,_,_,.iso chart,z,t => C.CertificateGeometryAgreement chart z t
  | _,_,_,_,_,.step W head tail,z,t =>
      C.VolumeObjectAgreement W z t ∧ C.BlowupGeometryAgreement head z t ∧ C.ChainGeometryAgreement tail z t

def GammaVolumeParameterRecode.CommonGeometryAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.leftObject z t ∧ C.VolumeObjectAgreement H.rightObject z t ∧
    C.ChainGeometryAgreement H.leftChain z t ∧ C.ChainGeometryAgreement H.rightChain z t ∧
      C.CertificateGeometryAgreement H.comparison z t

theorem GammaVolumeParameterRecode.blowupWithFrozenParameters_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hU : C.VolumeObjectAgreement F z t) (hV : C.VolumeObjectAgreement G z t)
    (h : C.BlowupGeometryAgreement H z t) (hValid : H.valid z) : (C.blowupWithFrozenParameters H).valid t := by
  rcases hValid with ⟨hF,hG,hA,hR,hAd,hS,hT,hSF,hSA,hTG,hTA⟩
  have hAR := C.volumeObject_rows H.center z t h.1
  have hRR := C.volumeObject_rows H.remainder z t h.2.1
  have hSR := h.2.2.1
  have hTR := h.2.2.2
  refine ⟨C.volumeObject_valid F z t ht hU hF,C.volumeObject_valid G z t ht hV hG,
    C.volumeObject_valid H.center z t ht h.1 hA,C.volumeObject_valid H.remainder z t ht h.2.1 hR,
    ?_,C.certificateWithFrozenParameters_valid H.sourceChart z t ht hSR hS,
    C.certificateWithFrozenParameters_valid H.resultChart z t ht hTR hT,?_,?_,?_,?_⟩
  · exact H.admissibility.valid_of_rowAgreement (C.blowupWithFrozenParameters H).admissibility z t ht rfl rfl rfl hAR.1 hAd
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hSR.1)
      (C.volumeObject_rows _ z t hU) hSF
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hSR.2.1) (hAR.coprod hRR hz ht) hSA
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hTR.1)
      (C.volumeObject_rows _ z t hV) hTG
  · exact gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t hTR.2.1)
      ((hAR.elementary hz ht).coprod hRR hz ht) hTA

theorem GammaVolumeParameterRecode.chainWithFrozenParameters_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeChainSchema F G r) : ∀ (z : Fin p → M) (t : Fin q → M),
      (∀ i, sortEval (sp i) (z i)) → (∀ i, sortEval (sq i) (t i)) →
      C.VolumeObjectAgreement F z t → C.VolumeObjectAgreement G z t →
      C.ChainGeometryAgreement H z t → H.valid z → (C.chainWithFrozenParameters H).valid t := by
  induction H with
  | iso chart =>
    intro z t hz ht hU hV h hValid
    exact ⟨C.certificateWithFrozenParameters_valid chart z t ht h hValid.1,
      gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.1)
        (C.volumeObject_rows _ z t hU) hValid.2.1,
      gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.1)
        (C.volumeObject_rows _ z t hV) hValid.2.2⟩
  | step W head tail ih =>
    intro z t hz ht hU hV h hValid
    exact ⟨C.volumeObject_valid W z t ht h.1 hValid.1,
      C.blowupWithFrozenParameters_valid head z t hz ht hU h.1 h.2.1 hValid.2.1,
      ih z t hz ht h.1 hV h.2.2 hValid.2.2⟩

theorem GammaVolumeParameterRecode.commonWithFrozenParameters_valid (C : GammaVolumeParameterRecode B p q sp sq)
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hU : C.VolumeObjectAgreement F z t) (hV : C.VolumeObjectAgreement G z t)
    (h : C.CommonGeometryAgreement H z t) (hValid : H.valid z) : (C.commonWithFrozenParameters H).valid t := by
  rcases hValid with ⟨hF,hG,hL,hR,hlc,hrc,hCmp,hCmpL,hCmpR⟩
  exact ⟨C.volumeObject_valid F z t ht hU hF,C.volumeObject_valid G z t ht hV hG,
    C.volumeObject_valid H.leftObject z t ht h.1 hL,C.volumeObject_valid H.rightObject z t ht h.2.1 hR,
    C.chainWithFrozenParameters_valid H.leftChain z t hz ht hU h.1 h.2.2.1 hlc,
    C.chainWithFrozenParameters_valid H.rightChain z t hz ht hV h.2.1 h.2.2.2.1 hrc,
    C.certificateWithFrozenParameters_valid H.comparison z t ht h.2.2.2.2 hCmp,
    gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.2.2.2.1)
      (C.volumeObject_rows _ z t h.1) hCmpL,
    gammaVolumeSameRow_of_agreement ht (C.volumeObject_rows _ z t h.2.2.2.2.2.1)
      (C.volumeObject_rows _ z t h.2.1) hCmpR⟩

end IntegrationInACVF.Section7
