import IntegrationSection6.GammaParameterRecoding

/-! Explicit primitive-row agreement for a formula recoding. This records
exactly the domain, volume and chart data needed to transport finite
witness validity; it does not postulate geometric uniformity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaParameterRecode.DomainAgreement (C : GammaParameterRecode B p q sp sq)
    (D : GammaDomainFormula B p a sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  ∀ x, Fin.append z x ∈ D.val ↔ Fin.append t x ∈ (C.domain D).val

def GammaParameterRecode.RelationAgreement (C : GammaParameterRecode B p q sp sq)
    (R : GammaRelationFormula B p a b sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  ∀ x y, Fin.append (Fin.append z x) y ∈ R.val ↔ Fin.append (Fin.append t x) y ∈ (C.relation R).val

def GammaParameterRecode.ObjectAgreement (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  GammaSchemaRowAgreement F z (C.object F) t

theorem GammaParameterRecode.objectAgreement_iff (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (t : Fin q → M) :
    C.ObjectAgreement F z t ↔ C.DomainAgreement ⟨F.domain,F.domain_definable⟩ z t ∧
      C.RelationAgreement ⟨F.volume,F.volume_definable⟩ z t := Iff.rfl

def GammaParameterRecode.IsoAgreement (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVIsoSchema B p a b k sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.ObjectAgreement F.source z t ∧ C.ObjectAgreement F.target z t ∧
    C.RelationAgreement ⟨F.chart,F.chart_definable⟩ z t

variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}

def GammaParameterRecode.BlowupAgreement (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteBlowupSchema U V) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.ObjectAgreement H.center z t ∧ C.ObjectAgreement H.remainder z t ∧
    C.IsoAgreement H.sourceChart z t ∧ C.IsoAgreement H.resultChart z t

def GammaParameterRecode.ChainAgreement (C : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → {U : GammaFiniteRVSchema B p a k sp} → {V : GammaFiniteRVSchema B p b k sp} → {r : ℕ} →
      GammaFiniteChainSchema U V r → (Fin p → M) → (Fin q → M) → Prop
  | _, _, _, _, _, .iso H, z, t => C.IsoAgreement H z t
  | _, _, _, _, _, .step W head tail, z, t =>
    C.ObjectAgreement W z t ∧ C.BlowupAgreement head z t ∧ C.ChainAgreement tail z t

def GammaParameterRecode.CommonAgreement (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteCommonSchema U V) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.ObjectAgreement H.leftObject z t ∧ C.ObjectAgreement H.rightObject z t ∧
    C.ChainAgreement H.leftChain z t ∧ C.ChainAgreement H.rightChain z t ∧ C.IsoAgreement H.comparison z t

end IntegrationInACVF.Section6
