import IntegrationSection6.GammaParameterRecoding

/-! Change the real/Gamma definition base of finite witness formulas
without changing any carrier, coordinate, bound or exact chain length. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaFormulaBaseChange (C B : Base (M := M)) where
  definable : ∀ {n : ℕ} (sn : Fin n → SortTag) (D : Set (Fin n → M)),
    DefinableOverBase C sn D → DefinableOverBase B sn D

variable {B C : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFormulaBaseChange.object (H : GammaFormulaBaseChange C B) (F : GammaFiniteRVSchema C p a k sp) :
    GammaFiniteRVSchema B p a k sp :=
  ⟨F.domain,F.volume,H.definable _ _ F.domain_definable,H.definable _ _ F.volume_definable,F.bound⟩

def GammaFormulaBaseChange.iso (H : GammaFormulaBaseChange C B) (F : GammaFiniteRVIsoSchema C p a b k sp) :
    GammaFiniteRVIsoSchema B p a b k sp :=
  ⟨H.object F.source,H.object F.target,F.chart,H.definable _ _ F.chart_definable⟩

def GammaFormulaBaseChange.admissibility (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteAdmissibilitySchema C p a k sp) : GammaFiniteAdmissibilitySchema B p a k sp :=
  ⟨H.object F.object,F.coordinate,F.bound⟩

variable {U : GammaFiniteRVSchema C p a k sp} {V : GammaFiniteRVSchema C p b k sp}

def GammaFormulaBaseChange.blowup (H : GammaFormulaBaseChange C B) (F : GammaFiniteBlowupSchema U V) :
    GammaFiniteBlowupSchema (H.object U) (H.object V) where
  centerArity := F.centerArity
  remainderArity := F.remainderArity
  center := H.object F.center
  remainder := H.object F.remainder
  coordinate := F.coordinate
  admissibilityBound := F.admissibilityBound
  sourceChart := H.iso F.sourceChart
  resultChart := H.iso F.resultChart

def GammaFormulaBaseChange.chain (H : GammaFormulaBaseChange C B) :
    {a b : ℕ} → {U : GammaFiniteRVSchema C p a k sp} → {V : GammaFiniteRVSchema C p b k sp} → {r : ℕ} →
      GammaFiniteChainSchema U V r → GammaFiniteChainSchema (H.object U) (H.object V) r
  | _,_,_,_,_,.iso F => .iso (H.iso F)
  | _,_,_,_,_,.step W head tail => .step (H.object W) (H.blowup head) (H.chain tail)

def GammaFormulaBaseChange.common (H : GammaFormulaBaseChange C B) (F : GammaFiniteCommonSchema U V) :
    GammaFiniteCommonSchema (H.object U) (H.object V) where
  leftArity := F.leftArity
  rightArity := F.rightArity
  leftObject := H.object F.leftObject
  rightObject := H.object F.rightObject
  leftLength := F.leftLength
  rightLength := F.rightLength
  leftChain := H.chain F.leftChain
  rightChain := H.chain F.rightChain
  comparison := H.iso F.comparison

theorem GammaFormulaBaseChange.object_valid (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteRVSchema C p a k sp) (z : Fin p → M) : (H.object F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.iso_valid (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteRVIsoSchema C p a b k sp) (z : Fin p → M) : (H.iso F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.admissibility_valid (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteAdmissibilitySchema C p a k sp) (z : Fin p → M) :
    (H.admissibility F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.blowup_valid (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteBlowupSchema U V) (z : Fin p → M) : (H.blowup F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.chain_valid (H : GammaFormulaBaseChange C B)
    {r : ℕ} (F : GammaFiniteChainSchema U V r) (z : Fin p → M) :
    (H.chain F).valid z ↔ F.valid z := by
  induction F with
  | iso F => rfl
  | step W head tail ih => exact and_congr Iff.rfl (and_congr Iff.rfl ih)

theorem GammaFormulaBaseChange.common_valid (H : GammaFormulaBaseChange C B)
    (F : GammaFiniteCommonSchema U V) (z : Fin p → M) : (H.common F).valid z ↔ F.valid z :=
  and_congr Iff.rfl (and_congr Iff.rfl (and_congr (H.chain_valid F.leftChain z)
    (and_congr (H.chain_valid F.rightChain z) Iff.rfl)))

end IntegrationInACVF.Section6
