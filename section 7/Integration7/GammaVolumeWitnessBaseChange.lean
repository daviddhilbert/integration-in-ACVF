module

public import Integration7.GammaVolumeFormulaBaseChange
public import Integration7.GammaVolumeWitnessValidity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Definable base changes preserve full volume blowup schemata,
their exact chain lengths and validity, including auxiliary exceptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

open IntegrationInACVF.Section7

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable {a b : ℕ} {U : GammaRVVolumeSchema C p a k sp} {V : GammaRVVolumeSchema C p b k sp}

def GammaFormulaBaseChange.volumeBlowup (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeBlowupSchema U V) : GammaRVVolumeBlowupSchema (H.volumeObject U) (H.volumeObject V) where
  centerArity := F.centerArity
  remainderArity := F.remainderArity
  center := H.volumeObject F.center
  remainder := H.volumeObject F.remainder
  admissibilityBound := F.admissibilityBound
  sourceChart := H.volumeCertificate F.sourceChart
  resultChart := H.volumeCertificate F.resultChart

def GammaFormulaBaseChange.volumeChain (H : GammaFormulaBaseChange C B) :
    {a b : ℕ} → {U : GammaRVVolumeSchema C p a k sp} → {V : GammaRVVolumeSchema C p b k sp} → {r : ℕ} →
      GammaVolumeChainSchema U V r → GammaVolumeChainSchema (H.volumeObject U) (H.volumeObject V) r
  | _,_,_,_,_,.iso F => .iso (H.volumeCertificate F)
  | _,_,_,_,_,.step W head tail => .step (H.volumeObject W) (H.volumeBlowup head) (H.volumeChain tail)

def GammaFormulaBaseChange.volumeCommon (H : GammaFormulaBaseChange C B)
    (F : GammaVolumeCommonSchema U V) : GammaVolumeCommonSchema (H.volumeObject U) (H.volumeObject V) where
  leftArity := F.leftArity
  rightArity := F.rightArity
  leftObject := H.volumeObject F.leftObject
  rightObject := H.volumeObject F.rightObject
  leftLength := F.leftLength
  rightLength := F.rightLength
  leftChain := H.volumeChain F.leftChain
  rightChain := H.volumeChain F.rightChain
  comparison := H.volumeCertificate F.comparison

theorem GammaFormulaBaseChange.volumeBlowup_valid (H : GammaFormulaBaseChange C B)
    (F : GammaRVVolumeBlowupSchema U V) (z : Fin p → M) :
    (H.volumeBlowup F).valid z ↔ F.valid z := Iff.rfl

theorem GammaFormulaBaseChange.volumeChain_valid (H : GammaFormulaBaseChange C B)
    {r : ℕ} (F : GammaVolumeChainSchema U V r) (z : Fin p → M) :
    (H.volumeChain F).valid z ↔ F.valid z := by
  induction F with
  | iso F => rfl
  | step W head tail ih => exact and_congr Iff.rfl (and_congr Iff.rfl ih)

theorem GammaFormulaBaseChange.volumeCommon_valid (H : GammaFormulaBaseChange C B)
    (F : GammaVolumeCommonSchema U V) (z : Fin p → M) :
    (H.volumeCommon F).valid z ↔ F.valid z :=
  and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (H.volumeChain_valid F.leftChain z) (and_congr (H.volumeChain_valid F.rightChain z) Iff.rfl)))))

theorem GammaFormulaBaseChange.volumeChain_noAuxiliary (H : GammaFormulaBaseChange C B)
    {r : ℕ} (F : GammaVolumeChainSchema U V r) :
    (H.volumeChain F).NoAuxiliary ↔ F.NoAuxiliary := by
  induction F with
  | iso F => rfl
  | step W head tail ih => exact and_congr Iff.rfl ih

theorem GammaFormulaBaseChange.volumeCommon_noAuxiliary (H : GammaFormulaBaseChange C B)
    (F : GammaVolumeCommonSchema U V) : (H.volumeCommon F).NoAuxiliary ↔ F.NoAuxiliary :=
  and_congr (H.volumeChain_noAuxiliary F.leftChain)
    (and_congr (H.volumeChain_noAuxiliary F.rightChain) Iff.rfl)

end IntegrationInACVF.Section6
