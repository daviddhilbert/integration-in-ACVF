import Integration7.UnarySpecialHeadPreparations
import IntegrationSection5.GammaPreparedBijection

/-! Actual unary special preparations over a VF field base, with the
original Gamma certificate and no additional parameter names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

theorem field_base_unary_special_preparation
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) 1 a) :
    ∃ b : ℕ, ∃ B : DefSet (M := M) (C.base : Set M) 1 b, ∃ T : SpecialBijection A B,
      GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain ∧ IsRVPullback (carrier B) := by
  let P : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let L := gammaLogicInput P
  let f := constantRVMap A 0
  have hf := L.real_map_graph f
  obtain ⟨b,B,T,_,hT,hB,_⟩ := gamma_map_preparation_at_boundary
    C.model00 Values.presentationValuation Values.presentation_compatible
    (uniformVerticalObstacles C.saturated C.small Values.presentationValuation Values.presentation_compatible)
    L (gammaPolynomialSupportInput_of_fieldBase P FBase) (Set.Subset.refl _) A
    (L.real_set _ (setDefinable A)) f hf none (by intro h; cases h)
  exact ⟨b,B,T,hT,hB⟩
end IntegrationInACVF.Section7
