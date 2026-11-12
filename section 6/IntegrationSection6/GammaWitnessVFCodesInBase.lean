import IntegrationSection6.GammaWitnessVFCodes
import IntegrationSection6.GammaFormulaBaseChange

/-! Code the primitive rows of original-base witnesses in a larger
coefficient field base. The predicate determined by the code still refers
to the unchanged original witness formulas and lengths. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p a b k : ℕ}

theorem gamma_domain_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (D : GammaDomainFormula B p a (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).DomainAgreement D) :=
  gamma_domain_vf_code FC ⟨D.val,H.definable _ _ D.property⟩

theorem gamma_relation_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (D : GammaRelationFormula B p a b (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).RelationAgreement D) :=
  gamma_relation_vf_code FC ⟨D.val,H.definable _ _ D.property⟩

theorem gamma_object_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaFiniteRVSchema B p a k (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement F) :=
  (gamma_domain_vf_code_in_base H FC ⟨F.domain,F.domain_definable⟩).and
    (gamma_relation_vf_code_in_base H FC ⟨F.volume,F.volume_definable⟩)

theorem gamma_iso_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaFiniteRVIsoSchema B p a b k (fun _ => .vf)) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).IsoAgreement F) :=
  (gamma_object_vf_code_in_base H FC F.source).and ((gamma_object_vf_code_in_base H FC F.target).and
    (gamma_relation_vf_code_in_base H FC ⟨F.chart,F.chart_definable⟩))

variable {U : GammaFiniteRVSchema B p a k (fun _ => .vf)} {V : GammaFiniteRVSchema B p b k (fun _ => .vf)}

theorem gamma_blowup_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaFiniteBlowupSchema U V) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement F) :=
  (gamma_object_vf_code_in_base H FC F.center).and ((gamma_object_vf_code_in_base H FC F.remainder).and
    ((gamma_iso_vf_code_in_base H FC F.sourceChart).and (gamma_iso_vf_code_in_base H FC F.resultChart)))

theorem gamma_chain_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    {r : ℕ} (F : GammaFiniteChainSchema U V r) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).ChainAgreement F) := by
  induction F with
  | iso F => exact gamma_iso_vf_code_in_base H FC F
  | step W head tail ih =>
    exact (gamma_object_vf_code_in_base H FC W).and ((gamma_blowup_vf_code_in_base H FC head).and ih)

theorem gamma_common_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (F : GammaFiniteCommonSchema U V) :
    GammaVFRowCode C p ((GammaParameterRecode.identity B p (fun _ => .vf)).CommonAgreement F) :=
  (gamma_object_vf_code_in_base H FC F.leftObject).and ((gamma_object_vf_code_in_base H FC F.rightObject).and
    ((gamma_chain_vf_code_in_base H FC F.leftChain).and ((gamma_chain_vf_code_in_base H FC F.rightChain).and
      (gamma_iso_vf_code_in_base H FC F.comparison))))

theorem gamma_common_cover_vf_code_in_base (H : GammaFormulaBaseChange B C) (FC : VFFieldBase C.real)
    (J : Finset (GammaFiniteCommonSchema U V)) :
    GammaVFRowCode C p (fun z t =>
      (GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement U z t ∧
      (GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement V z t ∧
      ∀ F ∈ J, (GammaParameterRecode.identity B p (fun _ => .vf)).CommonAgreement F z t) :=
  (gamma_object_vf_code_in_base H FC U).and ((gamma_object_vf_code_in_base H FC V).and
    (GammaVFRowCode.finset J _ (fun F _ => gamma_common_vf_code_in_base H FC F)))

end IntegrationInACVF.Section6
