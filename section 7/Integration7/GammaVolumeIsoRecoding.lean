import Integration7.GammaVolumeParameterRecoding
import Integration7.VolumeIsoSchemaRowTransport
import Integration7.ZeroAuxVolumeCertificateSemantics
import IntegrationSection6.GammaRecodingValidity

/-! Exact primitive rows transport complete volume-isomorphism
certificates, including the supported RV clause and finite exception map. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeParameterRecode.isoSchema (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoSchema B p a b k sp) : GammaRVVolumeIsoSchema B q a b k sq where
  source := C.volumeObject H.source
  target := C.volumeObject H.target
  chart := (C.formulas.relation ⟨H.chart,H.chart_definable⟩).val
  chart_definable := (C.formulas.relation ⟨H.chart,H.chart_definable⟩).property
  supports := H.supports
  exceptionDegree := H.exceptionDegree
  exceptionDegree_lt := H.exceptionDegree_lt
  exception := C.formulas.object H.exception

def GammaVolumeParameterRecode.IsoAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.source z t ∧ C.VolumeObjectAgreement H.target z t ∧
    C.formulas.RelationAgreement ⟨H.chart,H.chart_definable⟩ z t ∧ C.formulas.ObjectAgreement H.exception z t

theorem GammaVolumeParameterRecode.isoSchema_valid (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ i, sortEval (sq i) (t i)) (h : C.IsoAgreement H z t) (hV : H.valid z) :
    (C.isoSchema H).valid t := by
  rcases hV with ⟨hF,hG,hOrd,hE,hΓ,hRV⟩
  have hS := C.volumeObject_rows H.source z t h.1
  have hT := C.volumeObject_rows H.target z t h.2.1
  refine ⟨C.volumeObject_valid H.source z t ht h.1 hF,
    C.volumeObject_valid H.target z t ht h.2.1 hG,?_,?_,?_,?_⟩
  · exact H.ordinary.valid_of_rowAgreement (C.isoSchema H).ordinary z t ht rfl rfl
      (essentialFiniteVolumeSchema_rowAgreement hS.1) (essentialFiniteVolumeSchema_rowAgreement hT.1)
      h.2.2.1 hOrd
  · exact C.formulas.object_valid H.exception z t ht h.2.2.2 hE
  · exact volumeChartGammaRowValid_of_rowAgreement hF.1.1 ht hS hT h.2.2.1 hΓ
  · exact volumeChartRVRowValid_of_rowAgreement hF.1.1 ht hS hT h.2.2.1 h.2.2.2 H.supports hRV

def GammaVolumeParameterRecode.certificate (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0) :
    GammaRVVolumeIsoCertificateSchema B q a b k sq :=
  (C.isoSchema (H.withoutAuxiliary h)).toCertificate

def GammaVolumeParameterRecode.CertificateAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0)
    (z : Fin p → M) (t : Fin q → M) : Prop := C.IsoAgreement (H.withoutAuxiliary h) z t

theorem GammaVolumeParameterRecode.certificate_valid (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (hAux : H.extraArity = 0)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ i, sortEval (sq i) (t i))
    (h : C.CertificateAgreement H hAux z t) (hV : H.valid z) : (C.certificate H hAux).valid t :=
  (C.isoSchema (H.withoutAuxiliary hAux)).toCertificate_valid t
    (C.isoSchema_valid (H.withoutAuxiliary hAux) z t ht h (H.withoutAuxiliary_valid hAux z hV))

@[simp] theorem GammaVolumeParameterRecode.certificate_noAuxiliary
    (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0) :
    (C.certificate H h).extraArity = 0 := rfl

end IntegrationInACVF.Section7
