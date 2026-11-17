module

public import Integration7.UnaryCompatiblePreparationWithoutField
public import Integration7.GammaSpecialCommonNames
public import IntegrationSection5.GammaGraphOperations
public import Section3.ModelContext

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Genuine unary pullback preparation in a prescribed small common-name
context. Generated field names and arbitrary internal code sets are
eliminated from the actual special chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {m : ℕ}

theorem gamma_unary_pullback_preparation_over_common_names
    (C : BaseContext M) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ P.gamma) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) 1 m) (hA : GammaSetDefinable P (carrier A)) :
    ∃ k : ℕ, ∃ B : DefSet (M := M) (C.base : Set M) 1 k,
      ∃ T : SpecialBijection A B, GammaChainDefinable P T.chain ∧ IsRVPullback (carrier B) := by
  have hPC : P.real ⊆ (C.base : Set M) := fun _ hx => hNames (Or.inl hx)
  have hsmall : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
  obtain ⟨R,hSR,k,l,B,D,T,U,hT,hU,hB,hD,_⟩ := lemma_5_2_gamma_presented_without_field
    C.uncountable C.saturated hsmall C.model00 γ hγ hγ1 hPC (Map.id A) Function.bijective_id hA hA
    (gamma_identity_graph A hA)
  exact ⟨k,gammaNativePresentation B (hT.target P T.chain) hNames,
    gammaSpecialPresentation T hT hNames,gamma_chain_presentation_gamma T.chain hT hNames,hB⟩

end IntegrationInACVF.Section7
