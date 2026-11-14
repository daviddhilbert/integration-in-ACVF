import Integration7.GammaVolumeWitnessValidity
import IntegrationSection6.GammaWitnessVFCodes

/-! A finite RV code determines the complete primitive formulas of a
volume witness, including its density and exceptional-set rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

def GammaVolumeParameterRecode.identity (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) :
    GammaVolumeParameterRecode B p p sp sp := ⟨GammaParameterRecode.identity B p sp⟩

theorem gamma_volume_object_vf_code (FBase : VFFieldBase B.real)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement F) :=
  (gamma_object_vf_code FBase F.object).and
    (gamma_relation_vf_code FBase ⟨F.density,F.density_definable⟩)

theorem gamma_volume_iso_vf_code (FBase : VFFieldBase B.real)
    (H : GammaRVVolumeIsoSchema B p a b k (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).IsoAgreement H) :=
  (gamma_volume_object_vf_code FBase H.source).and ((gamma_volume_object_vf_code FBase H.target).and
    ((gamma_relation_vf_code FBase ⟨H.chart,H.chart_definable⟩).and
      (gamma_object_vf_code FBase H.exception)))

theorem gamma_volume_certificate_vf_code (FBase : VFFieldBase B.real)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .vf)) (h : H.extraArity = 0) :
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CertificateAgreement H h) :=
  gamma_volume_iso_vf_code FBase (H.withoutAuxiliary h)

variable {U : GammaRVVolumeSchema B p a k (fun _ => .vf)}
variable {V : GammaRVVolumeSchema B p b k (fun _ => .vf)}

theorem gamma_volume_blowup_vf_code (FBase : VFFieldBase B.real)
    (H : GammaRVVolumeBlowupSchema U V) (h : H.NoAuxiliary) :
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement H h) :=
  (gamma_volume_object_vf_code FBase H.center).and ((gamma_volume_object_vf_code FBase H.remainder).and
    ((gamma_volume_certificate_vf_code FBase H.sourceChart h.1).and
      (gamma_volume_certificate_vf_code FBase H.resultChart h.2)))

theorem gamma_volume_chain_vf_code (FBase : VFFieldBase B.real) {r : ℕ}
    (H : GammaVolumeChainSchema U V r) : ∀ h : H.NoAuxiliary,
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).ChainAgreement H h) := by
  induction H with
  | iso H => exact fun h => gamma_volume_certificate_vf_code FBase H h
  | step W head tail ih =>
    exact fun h => (gamma_volume_object_vf_code FBase W).and
      ((gamma_volume_blowup_vf_code FBase head h.1).and (ih h.2))

theorem gamma_volume_common_vf_code (FBase : VFFieldBase B.real)
    (H : GammaVolumeCommonSchema U V) (h : H.NoAuxiliary) :
    GammaVFRowCode B p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H h) :=
  (gamma_volume_object_vf_code FBase H.leftObject).and ((gamma_volume_object_vf_code FBase H.rightObject).and
    ((gamma_volume_chain_vf_code FBase H.leftChain h.1).and
      ((gamma_volume_chain_vf_code FBase H.rightChain h.2.1).and
        (gamma_volume_certificate_vf_code FBase H.comparison h.2.2))))

theorem gamma_volume_common_cover_vf_code (FBase : VFFieldBase B.real)
    (J : Finset {H : GammaVolumeCommonSchema U V // H.NoAuxiliary}) :
    GammaVFRowCode B p (fun z t =>
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement U z t ∧
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement V z t ∧
      ∀ H ∈ J, (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H.val H.property z t) :=
  (gamma_volume_object_vf_code FBase U).and ((gamma_volume_object_vf_code FBase V).and
    (GammaVFRowCode.finset J _ (fun H _ => gamma_volume_common_vf_code FBase H.val H.property)))

end IntegrationInACVF.Section7
