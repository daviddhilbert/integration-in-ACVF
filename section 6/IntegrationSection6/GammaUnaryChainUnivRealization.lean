import IntegrationSection6.GammaUnivPresentations
import IntegrationSection5.GammaUnaryChain

/-! Realize Gamma unary chains directly over the common internal universe,
without changing any domain, function, or mathematical parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

theorem gammaUnaryChain_univ_realization
    {U : Set (Point (M := M) n a)} {V : Set (Point (M := M) n b)} (T : GammaUnaryChain B n U V)
    (hU : GammaSetDefinable B U) (hV : GammaSetDefinable B V) :
    ∃ t : UnaryChain Set.univ n (gammaDefSetUniv U hU) (gammaDefSetUniv V hV),
      GammaUnaryChainDefinable B t := by
  induction T with
  | nil U hU' => exact ⟨.nil _,hU⟩
  | @cons a c b U W V i e hi tail ih =>
    have hW := e.target_definable (gammaLogicInput B)
    obtain ⟨t,ht⟩ := ih hW hV
    let f : Map (gammaDefSetUniv U hU) (gammaDefSetUniv W hW) :=
      Map.mk e.equiv (gammaGraph_univ_definable e.graph)
    exact ⟨.cons i f e.equiv.bijective hi t,⟨e.graph,ht⟩⟩

end IntegrationInACVF.Section6
