import IntegrationSection6.GammaPrimitiveVFCodes

/-! An entire finite common-blowup witness has one finite RV code over
the original real parameter base. All internal chart formulas are included. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}
variable {U : GammaFiniteRVSchema B p a k (fun _ => .vf)}
variable {V : GammaFiniteRVSchema B p b k (fun _ => .vf)}

theorem gamma_blowup_vf_code (FBase : VFFieldBase B.real) (H : GammaFiniteBlowupSchema U V) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement H) :=
  (gamma_object_vf_code FBase H.center).and ((gamma_object_vf_code FBase H.remainder).and
    ((gamma_iso_vf_code FBase H.sourceChart).and (gamma_iso_vf_code FBase H.resultChart)))

theorem gamma_chain_vf_code (FBase : VFFieldBase B.real) {r : ℕ} (H : GammaFiniteChainSchema U V r) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).ChainAgreement H) := by
  induction H with
  | iso H => exact gamma_iso_vf_code FBase H
  | step W head tail ih =>
    exact (gamma_object_vf_code FBase W).and ((gamma_blowup_vf_code FBase head).and ih)

theorem gamma_common_vf_code (FBase : VFFieldBase B.real) (H : GammaFiniteCommonSchema U V) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H) :=
  (gamma_object_vf_code FBase H.leftObject).and ((gamma_object_vf_code FBase H.rightObject).and
    ((gamma_chain_vf_code FBase H.leftChain).and ((gamma_chain_vf_code FBase H.rightChain).and
      (gamma_iso_vf_code FBase H.comparison))))

theorem gamma_common_cover_vf_code (FBase : VFFieldBase B.real)
    (J : Finset (GammaFiniteCommonSchema U V)) :
    GammaVFRowCode B p (fun z t =>
      (GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement U z t ∧
      (GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement V z t ∧
      ∀ H ∈ J, (GammaParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H z t) :=
  (gamma_object_vf_code FBase U).and ((gamma_object_vf_code FBase V).and
    (GammaVFRowCode.finset J _ (fun H _ => gamma_common_vf_code FBase H)))

end IntegrationInACVF.Section6
