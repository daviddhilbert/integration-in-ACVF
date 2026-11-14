import Integration7.GammaVolumeChainSchemata

/-! Witnesses obtained over the named term context can retain their
exception maps without adding another parameter block. This property is
recorded explicitly for subsequent VF-to-RV formula preparation. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k r : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeBlowupSchema.NoAuxiliary
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaRVVolumeBlowupSchema F G) : Prop :=
  H.sourceChart.extraArity = 0 ∧ H.resultChart.extraArity = 0

def GammaVolumeChainSchema.NoAuxiliary :
    {a b : ℕ} → {F : GammaRVVolumeSchema B p a k sp} → {G : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → GammaVolumeChainSchema F G r → Prop
  | _,_,_,_,_,.iso chart => chart.extraArity = 0
  | _,_,_,_,_,.step _ head tail => head.NoAuxiliary ∧ tail.NoAuxiliary

def GammaVolumeCommonSchema.NoAuxiliary
    {F : GammaRVVolumeSchema B p a k sp} {G : GammaRVVolumeSchema B p b k sp}
    (H : GammaVolumeCommonSchema F G) : Prop :=
  H.leftChain.NoAuxiliary ∧ H.rightChain.NoAuxiliary ∧ H.comparison.extraArity = 0

end IntegrationInACVF.Section7
