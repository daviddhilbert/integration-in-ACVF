import IntegrationSection6.GammaCommonBlowupSchemata
import IntegrationSection6.GammaSchemaRowAgreement

/-! Recode domain and relation formulas into a new sorted parameter block.
Finite-object metadata, admissible coordinates and exact witness lengths
are preserved by construction. Prepared RV descent supplies this operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

abbrev GammaDomainFormula (B : Base (M := M)) (p a : ℕ) (sp : Fin p → SortTag) :=
  {D : Set (Fin (p+a) → M) // DefinableOverBase B (Fin.append sp (fun _ : Fin a => .rv)) D}

abbrev GammaRelationFormula (B : Base (M := M)) (p a b : ℕ) (sp : Fin p → SortTag) :=
  {R : Set (Fin ((p+a)+b) → M) // DefinableOverBase B
    (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) R}

structure GammaParameterRecode (B : Base (M := M)) (p q : ℕ)
    (sp : Fin p → SortTag) (sq : Fin q → SortTag) where
  domain : ∀ {a}, GammaDomainFormula B p a sp → GammaDomainFormula B q a sq
  relation : ∀ {a b}, GammaRelationFormula B p a b sp → GammaRelationFormula B q a b sq

variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def GammaParameterRecode.object (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) : GammaFiniteRVSchema B q a k sq :=
  let D := C.domain ⟨F.domain,F.domain_definable⟩
  let V := C.relation ⟨F.volume,F.volume_definable⟩
  ⟨D.val,V.val,D.property,V.property,F.bound⟩

theorem GammaParameterRecode.object_bound (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVSchema B p a k sp) : F.bound = (C.object F).bound := rfl

def GammaParameterRecode.iso (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteRVIsoSchema B p a b k sp) : GammaFiniteRVIsoSchema B q a b k sq :=
  let H := C.relation ⟨F.chart,F.chart_definable⟩
  ⟨C.object F.source,C.object F.target,H.val,H.property⟩

def GammaParameterRecode.admissibility (C : GammaParameterRecode B p q sp sq)
    (F : GammaFiniteAdmissibilitySchema B p a k sp) : GammaFiniteAdmissibilitySchema B q a k sq :=
  ⟨C.object F.object,F.coordinate,F.bound⟩

variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}

def GammaParameterRecode.blowup (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteBlowupSchema U V) : GammaFiniteBlowupSchema (C.object U) (C.object V) where
  centerArity := H.centerArity
  remainderArity := H.remainderArity
  center := C.object H.center
  remainder := C.object H.remainder
  coordinate := H.coordinate
  admissibilityBound := H.admissibilityBound
  sourceChart := C.iso H.sourceChart
  resultChart := C.iso H.resultChart

def GammaParameterRecode.chain (C : GammaParameterRecode B p q sp sq) :
    {a b : ℕ} → {U : GammaFiniteRVSchema B p a k sp} → {V : GammaFiniteRVSchema B p b k sp} → {r : ℕ} →
      GammaFiniteChainSchema U V r → GammaFiniteChainSchema (C.object U) (C.object V) r
  | _, _, _, _, _, .iso H => .iso (C.iso H)
  | _, _, _, _, _, .step W head tail => .step (C.object W) (C.blowup head) (C.chain tail)

def GammaParameterRecode.common (C : GammaParameterRecode B p q sp sq)
    (H : GammaFiniteCommonSchema U V) : GammaFiniteCommonSchema (C.object U) (C.object V) where
  leftArity := H.leftArity
  rightArity := H.rightArity
  leftObject := C.object H.leftObject
  rightObject := C.object H.rightObject
  leftLength := H.leftLength
  rightLength := H.rightLength
  leftChain := C.chain H.leftChain
  rightChain := C.chain H.rightChain
  comparison := C.iso H.comparison

end IntegrationInACVF.Section6
