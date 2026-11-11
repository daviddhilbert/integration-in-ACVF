import IntegrationSection5.GammaChainAlgebra
import Section5.Centering

/-! Finish an actual unary chain with a tagged target, preserving strict
alternation. An existing final canonical step is reused. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem gamma_tagged_tail (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain) :
    ∃ r : ℕ, ∃ C : DefSet (M := M) S 1 r, ∃ U : SpecialBijection B C,
      U.chain.Alternating (T.chain.lastKind none) ∧ GammaChainDefinable P U.chain ∧
      U.chain.lastKind (T.chain.lastKind none) = some false ∧
      ∃ j : Fin r, Tagged (carrier C) 0 j := by
  have hB := GammaChainDefinable.target P T.chain hT
  by_cases he : T.chain.lastKind none = some false
  · refine ⟨l,B,SpecialBijection.refl B,trivial,hB,he,?_⟩
    exact T.chain.lastKind_tagged none (by intro h; cases h) he
  · let U := SpecialBijection.canonical B
    have hC := GammaPrimitiveDefinable.target (gammaLogicInput P) (.canonical B) hB
    refine ⟨1+l,canonicalImage B,U,⟨he,trivial⟩,⟨hB,hC⟩,rfl,?_⟩
    refine ⟨Fin.castAdd l 0,?_⟩
    rw [canonicalImage_carrier]
    exact canonical_tagged (carrier B) 0

end IntegrationInACVF.Section5
