import IntegrationSection6.GammaFormulaVFFamilies
import IntegrationSection6.GammaVFCodePairing
import IntegrationSection6.GammaRecodingAgreements

/-! Finite RV codes determine every raw domain, volume and isomorphism
chart row, including the falsity of rows on improper RV tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

def GammaParameterRecode.identity (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) :
    GammaParameterRecode B p p sp sp := ⟨id,id⟩

theorem gamma_domain_vf_code (FBase : VFFieldBase B.real)
    (D : GammaDomainFormula B p a (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).DomainAgreement D) := by
  obtain ⟨d,g,hg,hrows⟩ := gamma_rv_family_finite_code FBase D.vfRelation D.vfRelation_definable
  refine ⟨d,g,hg,?_⟩
  intro x y he
  exact gammaDomainRows_agree_of_typed D D _ _ (fun u => hrows x y he (Fin.elim0,u))

theorem gamma_relation_vf_code (FBase : VFFieldBase B.real)
    (R : GammaRelationFormula B p a b (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).RelationAgreement R) := by
  obtain ⟨d,g,hg,hrows⟩ := gamma_rv_family_finite_code FBase R.vfRelation R.vfRelation_definable
  refine ⟨d,g,hg,?_⟩
  intro x y he
  apply gammaRelationRows_agree_of_typed R R
  intro u v
  simpa only [GammaRelationFormula.vfRelation_append] using hrows x y he (Fin.elim0,Fin.append u v)

theorem gamma_object_vf_code (FBase : VFFieldBase B.real)
    (F : GammaFiniteRVSchema B p a k (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement F) :=
  (gamma_domain_vf_code FBase ⟨F.domain,F.domain_definable⟩).and
    (gamma_relation_vf_code FBase ⟨F.volume,F.volume_definable⟩)

theorem gamma_iso_vf_code (FBase : VFFieldBase B.real)
    (F : GammaFiniteRVIsoSchema B p a b k (fun _ => .vf)) :
    GammaVFRowCode B p ((GammaParameterRecode.identity B p (fun _ => .vf)).IsoAgreement F) :=
  (gamma_object_vf_code FBase F.source).and ((gamma_object_vf_code FBase F.target).and
    (gamma_relation_vf_code FBase ⟨F.chart,F.chart_definable⟩))

end IntegrationInACVF.Section6
