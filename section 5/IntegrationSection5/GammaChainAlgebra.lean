import IntegrationSection5.GammaPulledFocus
import IntegrationSection5.MatchedFocusStep

/-! Invariant graph certificates for matched special-chain operations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l r s : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
variable {C : DefSet (M := M) S n r}

theorem gamma_chain_append (T : Chain S n A B) (U : Chain S n B C)
    (hT : GammaChainDefinable P T) (hU : GammaChainDefinable P U) :
    GammaChainDefinable P (T.append U) := by
  induction T with
  | nil _ => exact hU
  | cons p tail ih => exact ⟨hT.1,ih U hT.2 hU⟩

theorem gamma_focussedCanonical {A : DefSet (M := M) S 1 m} {k : Fin m}
    (D : Focus A 0 k) (hA : GammaSetDefinable P (carrier A))
    (hD : GammaFocusDefinable P D) :
    GammaChainDefinable P (focussedCanonical D).chain := by
  have hEta := GammaPrimitiveDefinable.target (gammaLogicInput P) (.centripetal D) ⟨hA,hD⟩
  have hCan := GammaPrimitiveDefinable.target (gammaLogicInput P) (.canonical D.etaImage) hEta
  exact ⟨⟨hA,hD⟩,hEta,hCan⟩

theorem gamma_unaryConjugate_graph
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}
    (TA : SpecialBijection A A') (TB : SpecialBijection B B') (f : Map A B)
    (hTA : GammaChainDefinable P TA.chain) (hTB : GammaChainDefinable P TB.chain)
    (hf : GammaGraphDefinable P (pointMapGraph f)) :
    GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB f)) :=
  gamma_composition_graph _ _
    (gamma_composition_graph _ _ (gamma_inverse_graph (gammaLogicInput P) TA hTA) hf)
    (GammaChainDefinable.graph (gammaLogicInput P) TB.chain hTB)

end IntegrationInACVF.Section5
