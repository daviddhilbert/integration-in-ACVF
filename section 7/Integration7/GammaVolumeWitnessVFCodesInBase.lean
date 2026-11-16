module

public import Integration7.GammaVolumeWitnessVFCodes
public import Integration7.GammaVolumeFormulaBaseChange
public import IntegrationSection6.GammaWitnessVFCodesInBase

@[expose] public section

/-! Code unchanged volume-witness rows using an internal coefficient
field. The predicates still refer to the original witness and base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p a b k : ℕ}

theorem gamma_volume_object_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement F) :=
  (gamma_object_vf_code_in_base H FC F.object).and
    (gamma_relation_vf_code_in_base H FC ⟨F.density,F.density_definable⟩)

theorem gamma_volume_iso_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeIsoSchema B p a b k (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).IsoAgreement F) :=
  (gamma_volume_object_vf_code_in_base H FC F.source).and
    ((gamma_volume_object_vf_code_in_base H FC F.target).and
      ((gamma_relation_vf_code_in_base H FC ⟨F.chart,F.chart_definable⟩).and
        (gamma_object_vf_code_in_base H FC F.exception)))

theorem gamma_volume_certificate_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .vf)) (h : F.extraArity = 0) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CertificateAgreement F h) :=
  gamma_volume_iso_vf_code_in_base H FC (F.withoutAuxiliary h)

variable {U : GammaRVVolumeSchema B p a k (fun _ => .vf)}
variable {V : GammaRVVolumeSchema B p b k (fun _ => .vf)}

theorem gamma_volume_blowup_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeBlowupSchema U V) (h : F.NoAuxiliary) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement F h) :=
  (gamma_volume_object_vf_code_in_base H FC F.center).and
    ((gamma_volume_object_vf_code_in_base H FC F.remainder).and
      ((gamma_volume_certificate_vf_code_in_base H FC F.sourceChart h.1).and
        (gamma_volume_certificate_vf_code_in_base H FC F.resultChart h.2)))

theorem gamma_volume_chain_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    {r : ℕ} (F : GammaVolumeChainSchema U V r) : ∀ h : F.NoAuxiliary,
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).ChainAgreement F h) := by
  induction F with
  | iso F => exact fun h => gamma_volume_certificate_vf_code_in_base H FC F h
  | step W head tail ih =>
    exact fun h => (gamma_volume_object_vf_code_in_base H FC W).and
      ((gamma_volume_blowup_vf_code_in_base H FC head h.1).and (ih h.2))

theorem gamma_volume_common_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaVolumeCommonSchema U V) (h : F.NoAuxiliary) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonAgreement F h) :=
  (gamma_volume_object_vf_code_in_base H FC F.leftObject).and
    ((gamma_volume_object_vf_code_in_base H FC F.rightObject).and
      ((gamma_volume_chain_vf_code_in_base H FC F.leftChain h.1).and
        ((gamma_volume_chain_vf_code_in_base H FC F.rightChain h.2.1).and
          (gamma_volume_certificate_vf_code_in_base H FC F.comparison h.2.2))))

theorem gamma_volume_common_cover_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (J : Finset {F : GammaVolumeCommonSchema U V // F.NoAuxiliary}) :
    GammaVFRowCode C p (fun z t =>
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement U z t ∧
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement V z t ∧
      ∀ F ∈ J, (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonAgreement F.val F.property z t) :=
  (gamma_volume_object_vf_code_in_base H FC U).and
    ((gamma_volume_object_vf_code_in_base H FC V).and
      (GammaVFRowCode.finset J _ (fun F _ => gamma_volume_common_vf_code_in_base H FC F.val F.property)))

end IntegrationInACVF.Section7
