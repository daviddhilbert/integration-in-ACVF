import Integration7.GammaVolumeBlowupSchemata

/-! Finite formula witnesses for volume blowup chains and common forward
blowups. The zero-length case records a volume isomorphism. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

inductive GammaVolumeChainSchema :
    {a b : ℕ} → GammaRVVolumeSchema B p a k sp → GammaRVVolumeSchema B p b k sp → ℕ → Type
  | iso {a b} {U : GammaRVVolumeSchema B p a k sp} {V : GammaRVVolumeSchema B p b k sp}
      (chart : GammaRVVolumeIsoCertificateSchema B p a b k sp) : GammaVolumeChainSchema U V 0
  | step {a b c} {U : GammaRVVolumeSchema B p a k sp} {V : GammaRVVolumeSchema B p b k sp}
      (W : GammaRVVolumeSchema B p c k sp) {r}
      (head : GammaRVVolumeBlowupSchema U W) (tail : GammaVolumeChainSchema W V r) :
      GammaVolumeChainSchema U V (r+1)

variable {a b r : ℕ} {U : GammaRVVolumeSchema B p a k sp} {V : GammaRVVolumeSchema B p b k sp}

def GammaVolumeChainSchema.valid :
    {a b : ℕ} → {U : GammaRVVolumeSchema B p a k sp} → {V : GammaRVVolumeSchema B p b k sp} →
      {r : ℕ} → GammaVolumeChainSchema U V r → (Fin p → M) → Prop
  | _,_,U,V,_,.iso chart,z => chart.valid z ∧ chart.source.sameRow U z ∧ chart.target.sameRow V z
  | _,_,_,_,_,.step W head tail,z => W.valid z ∧ head.valid z ∧ tail.valid z

theorem GammaVolumeChainSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (H : GammaVolumeChainSchema U V r) : DefinableOverBase B sp {z | H.valid z} := by
  induction H with
  | iso chart =>
    exact (chart.valid_definable hc).inter
      ((chart.source.sameRow_definable _).inter (chart.target.sameRow_definable _))
  | step W head tail ih => exact W.valid_definable.inter ((head.valid_definable hc).inter ih)

structure GammaVolumeCommonSchema (U : GammaRVVolumeSchema B p a k sp)
    (V : GammaRVVolumeSchema B p b k sp) where
  leftArity : ℕ
  rightArity : ℕ
  leftObject : GammaRVVolumeSchema B p leftArity k sp
  rightObject : GammaRVVolumeSchema B p rightArity k sp
  leftLength : ℕ
  rightLength : ℕ
  leftChain : GammaVolumeChainSchema U leftObject leftLength
  rightChain : GammaVolumeChainSchema V rightObject rightLength
  comparison : GammaRVVolumeIsoCertificateSchema B p leftArity rightArity k sp

def GammaVolumeCommonSchema.valid (H : GammaVolumeCommonSchema U V) (z : Fin p → M) : Prop :=
  U.valid z ∧ V.valid z ∧ H.leftObject.valid z ∧ H.rightObject.valid z ∧
    H.leftChain.valid z ∧ H.rightChain.valid z ∧ H.comparison.valid z ∧
    H.comparison.source.sameRow H.leftObject z ∧ H.comparison.target.sameRow H.rightObject z

theorem GammaVolumeCommonSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (H : GammaVolumeCommonSchema U V) : DefinableOverBase B sp {z | H.valid z} :=
  U.valid_definable.inter (V.valid_definable.inter (H.leftObject.valid_definable.inter
    (H.rightObject.valid_definable.inter ((H.leftChain.valid_definable hc).inter
      ((H.rightChain.valid_definable hc).inter ((H.comparison.valid_definable hc).inter
        ((H.comparison.source.sameRow_definable H.leftObject).inter
          (H.comparison.target.sameRow_definable H.rightObject))))))))

end IntegrationInACVF.Section7
