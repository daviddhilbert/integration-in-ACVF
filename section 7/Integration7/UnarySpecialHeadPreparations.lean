import Integration7.GammaFixedRVLabelSpecialLifts
import Integration7.UnarySpecialRelativeConverse
import IntegrationSection5.HeadPreparation
import IntegrationSection5.GammaOrderedContraction

/-! An actual unary special bijection with RV-pullback target is an
actual head preparation. The fibre-special witnesses are transported
from that same chain, with no extra existence premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}

def unarySpecialHeadPreparation {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) : HeadPreparation A where
  arity := b
  target := B
  map := T.toMap
  special := unary_special_relative T
  saturated := by
    intro p hp x hx
    apply (isRVPullback_iff _).mp hB p hp (replace 0 p x)
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,rfl⟩
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [replace,vfAt,Function.update_self] using hx.symm

def unarySpecialContractionProgram {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) :
    OrderedContractionProgram S A (unarySpecialHeadPreparation T hB).contractedSet :=
  .step (unarySpecialHeadPreparation T hB) (.zero _)

theorem gamma_unary_special_contraction_program {P : Base (M := M)}
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) (hT : GammaChainDefinable P T.chain) :
    GammaProgramDefinable P (unarySpecialContractionProgram T hB) :=
  ⟨GammaChainDefinable.graph (gammaLogicInput P) T.chain hT,
    GammaChainDefinable.target P T.chain hT,
    gamma_headImage B (GammaChainDefinable.target P T.chain hT)⟩

end IntegrationInACVF.Section7
