module

public import IntegrationSection6.CompletedSection5TwoOrderInput
public import IntegrationSection6.GammaClosureIsomorphisms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Section5 two-order refinement descends through definable
parameter naming. The internal contractions and their finite RV objects
are unchanged; every complete program and isomorphism graph descends. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B D : Base (M := M)} {S : Set M}

theorem gamma_program_definable_base_reduction (H : GammaDefinableBaseReduction D B)
    {a b c : ℕ} {X : DefSet (M := M) S a b} {Y : DefSet (M := M) S 0 c}
    (T : OrderedContractionProgram S X Y) (hT : GammaProgramDefinable D T) :
    GammaProgramDefinable B T := by
  induction T with
  | zero A => exact H.definable hT
  | step T tail ih => exact ⟨H.definable hT.1,H.definable hT.2.1,ih hT.2.2⟩

theorem section5_two_order_input_base_reduction {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hB : Cardinal.mk B.real < κ) (hD : Cardinal.mk D.real < κ)
    (H : GammaDefinableBaseReduction D B) (hBD : B.gamma ⊆ D.gamma)
    (h58 : Section5TwoOrderInput D hκ hs hD) : Section5TwoOrderInput B hκ hs hB := by
  intro a U hU hfinU σ υ hNe
  obtain ⟨b,V,hV,hfinV,f,hf,hF,hVF,T,E,hT,hE,⟨e⟩⟩ :=
    h58 U (hU.mono H.real_subset hBD) hfinU σ υ hNe
  let hVB : GammaSetDefinable B (carrier V) := H.definable hV
  let hTB : GammaProgramDefinable B T.program := gamma_program_definable_base_reduction H T.program hT
  let hEB : GammaProgramDefinable B E.program := gamma_program_definable_base_reduction H E.program hE
  exact ⟨b,V,hVB,hfinV,f,hf,H.definable hF,hVF,T,E,hTB,hEB,
    ⟨⟨e.equiv,H.definable e.graph,e.weight,e.leftFinite,e.rightFinite⟩⟩⟩
end IntegrationInACVF.Section7
