module

public import Integration7.FrozenVolumeWitnessRecoding
public import Integration7.GammaVolumeWitnessVFCodesInBase

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Finite VF row codes for the geometric part of arbitrary volume
witnesses. Auxiliary exception parameters are retained separately and do
not enter the code or require an auxiliary-free hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p a b k : ℕ}

theorem volume_certificate_geometry_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CertificateGeometryAgreement F) :=
  (gamma_volume_object_vf_code_in_base H FC F.source).and
    ((gamma_volume_object_vf_code_in_base H FC F.target).and
      (gamma_relation_vf_code_in_base H FC ⟨F.chart,F.chart_definable⟩))

variable {U : GammaRVVolumeSchema B p a k (fun _ => .vf)}
variable {V : GammaRVVolumeSchema B p b k (fun _ => .vf)}

theorem volume_blowup_geometry_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaRVVolumeBlowupSchema U V) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).BlowupGeometryAgreement F) :=
  (gamma_volume_object_vf_code_in_base H FC F.center).and
    ((gamma_volume_object_vf_code_in_base H FC F.remainder).and
      ((volume_certificate_geometry_vf_code_in_base H FC F.sourceChart).and
        (volume_certificate_geometry_vf_code_in_base H FC F.resultChart)))

theorem volume_chain_geometry_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    {r : ℕ} (F : GammaVolumeChainSchema U V r) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).ChainGeometryAgreement F) := by
  induction F with
  | iso F => exact volume_certificate_geometry_vf_code_in_base H FC F
  | step W head tail ih =>
    exact (gamma_volume_object_vf_code_in_base H FC W).and
      ((volume_blowup_geometry_vf_code_in_base H FC head).and ih)

theorem volume_common_geometry_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaVolumeCommonSchema U V) :
    GammaVFRowCode C p ((GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonGeometryAgreement F) :=
  (gamma_volume_object_vf_code_in_base H FC F.leftObject).and
    ((gamma_volume_object_vf_code_in_base H FC F.rightObject).and
      ((volume_chain_geometry_vf_code_in_base H FC F.leftChain).and
        ((volume_chain_geometry_vf_code_in_base H FC F.rightChain).and
          (volume_certificate_geometry_vf_code_in_base H FC F.comparison))))

theorem volume_common_geometry_cover_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (J : Finset (GammaVolumeCommonSchema U V)) :
    GammaVFRowCode C p (fun z t =>
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement U z t ∧
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement V z t ∧
      ∀ F ∈ J, (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonGeometryAgreement F z t) :=
  (gamma_volume_object_vf_code_in_base H FC U).and
    ((gamma_volume_object_vf_code_in_base H FC V).and
      (GammaVFRowCode.finset J _ (fun F _ => volume_common_geometry_vf_code_in_base H FC F)))

end IntegrationInACVF.Section7
