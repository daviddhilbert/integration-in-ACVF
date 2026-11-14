import Integration7.GammaIgnoredParameterRecoding
import Integration7.ExtraVolumeRowTransport
import Integration7.GammaVolumeIsoRecoding

/-! General volume certificates recode their geometric formulas while
retaining the old parameter tuple existentially inside the exception map.
The old tuple is not added to geometric labels or to the fixed base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaVolumeParameterRecode.certificateWithFrozenParameters
    (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) : GammaRVVolumeIsoCertificateSchema B q a b k sq where
  source := C.volumeObject H.source
  target := C.volumeObject H.target
  chart := (C.formulas.relation ⟨H.chart,H.chart_definable⟩).val
  chart_definable := (C.formulas.relation ⟨H.chart,H.chart_definable⟩).property
  supports := H.supports
  extraArity := p+H.extraArity
  extraSort := Fin.append sp H.extraSort
  exceptionDegree := H.exceptionDegree
  exceptionDegree_lt := H.exceptionDegree_lt
  exception := (GammaParameterRecode.ignorePrefix B (Fin.append sp H.extraSort) sq).object H.exception

def GammaVolumeParameterRecode.CertificateGeometryAgreement
    (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.VolumeObjectAgreement H.source z t ∧ C.VolumeObjectAgreement H.target z t ∧
    C.formulas.RelationAgreement ⟨H.chart,H.chart_definable⟩ z t

theorem GammaVolumeParameterRecode.certificateWithFrozenParameters_valid
    (C : GammaVolumeParameterRecode B p q sp sq)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ i, sortEval (sq i) (t i))
    (h : C.CertificateGeometryAgreement H z t) (hV : H.valid z) :
    (C.certificateWithFrozenParameters H).valid t := by
  rcases hV with ⟨hF,hG,hOrd,hΓ,y,hE,hRV⟩
  have hS := C.volumeObject_rows H.source z t h.1
  have hT := C.volumeObject_rows H.target z t h.2.1
  have hE' := GammaParameterRecode.ignorePrefix_valid H.exception (Fin.append z y) t hE ht
  have hERows := GammaParameterRecode.ignorePrefix_rows H.exception (Fin.append z y) t hE.1 ht
  refine ⟨C.volumeObject_valid H.source z t ht h.1 hF,
    C.volumeObject_valid H.target z t ht h.2.1 hG,?_,?_,Fin.append z y,hE',?_⟩
  · exact H.ordinary.valid_of_rowAgreement (C.certificateWithFrozenParameters H).ordinary z t ht rfl rfl
      (essentialFiniteVolumeSchema_rowAgreement hS.1) (essentialFiniteVolumeSchema_rowAgreement hT.1) h.2.2 hOrd
  · exact volumeChartGammaRowValid_of_rowAgreement hF.1.1 ht hS hT h.2.2 hΓ
  · exact extraVolumeChartRVRowValid_of_rowAgreement hF.1.1 ht hS hT h.2.2 hERows hE'.1 H.supports hRV

end IntegrationInACVF.Section7
