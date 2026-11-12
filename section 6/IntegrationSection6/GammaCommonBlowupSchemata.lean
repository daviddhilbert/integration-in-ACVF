import IntegrationSection6.GammaChainSchemata

/-! Finite first-order witnesses for common forward blowups. Both chains,
all intermediate RV[k] objects, and the final weighted comparison chart
are explicit formula data; validity does not assume Isp definability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

structure GammaFiniteCommonSchema (U : GammaFiniteRVSchema B p a k sp)
    (V : GammaFiniteRVSchema B p b k sp) where
  leftArity : ℕ
  rightArity : ℕ
  leftObject : GammaFiniteRVSchema B p leftArity k sp
  rightObject : GammaFiniteRVSchema B p rightArity k sp
  leftLength : ℕ
  rightLength : ℕ
  leftChain : GammaFiniteChainSchema U leftObject leftLength
  rightChain : GammaFiniteChainSchema V rightObject rightLength
  comparison : GammaFiniteRVIsoSchema B p leftArity rightArity k sp

variable {U : GammaFiniteRVSchema B p a k sp} {V : GammaFiniteRVSchema B p b k sp}

def GammaFiniteCommonSchema.valid (H : GammaFiniteCommonSchema U V) (z : Fin p → M) : Prop :=
  H.leftObject.valid z ∧ H.rightObject.valid z ∧ H.leftChain.valid z ∧ H.rightChain.valid z ∧
  H.comparison.valid z ∧ H.comparison.source.sameRow H.leftObject z ∧ H.comparison.target.sameRow H.rightObject z

theorem GammaFiniteCommonSchema.valid_definable (H : GammaFiniteCommonSchema U V) :
    DefinableOverBase B sp {z | H.valid z} :=
  H.leftObject.valid_definable.inter (H.rightObject.valid_definable.inter
    (H.leftChain.valid_definable.inter (H.rightChain.valid_definable.inter
      (H.comparison.valid_definable.inter
        ((H.comparison.source.sameRow_definable H.leftObject).inter
          (H.comparison.target.sameRow_definable H.rightObject))))))

end IntegrationInACVF.Section6
