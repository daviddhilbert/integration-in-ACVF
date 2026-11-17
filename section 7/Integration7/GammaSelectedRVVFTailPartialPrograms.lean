module

public import Integration7.SelectedRVVFTailPartialPrograms
public import IntegrationSection5.GammaOrderedContraction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Lifted partial contractions retain the entire original-Gamma
certificate at every head and on the final selected-label domain. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a l d : ℕ}

theorem gamma_native_program_selected_rv_vf_tail_lift
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a)
    (hA : GammaSetDefinable G (carrier A)) :
    GammaSetDefinable G (carrier (nativeProgramSelectedRVVFTailLift hc A ρ)) :=
  gamma_native_vf_arity_cast (Nat.add_comm n d) _ (gamma_native_selected_rv_vf_tail_lift hc A ρ hA)

theorem gamma_selected_vf_program_tail_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a)
    (hA : GammaSetDefinable G (carrier A)) (hT : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaGraphDefinable G (pointMapGraph (T.selectedVFProgramTail hc ρ).map) :=
  gamma_native_vf_arity_cast_map (Nat.add_comm (n+1) d) _
    (gamma_native_selected_rv_vf_tail_map hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ) hA hT)

theorem gamma_selected_vf_program_tail_target
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a)
    (hT : GammaSetDefinable G (carrier T.target)) :
    GammaSetDefinable G (carrier (T.selectedVFProgramTail hc ρ).target) :=
  gamma_native_program_selected_rv_vf_tail_lift hc T.target (T.selectedTailIndex ρ) hT

theorem gamma_selected_rv_vf_tail_partial_program
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) :
    ∀ (hA : GammaSetDefinable G (carrier A)) (hT : GammaProgramDefinable G T) (ρ : Fin d → Fin a),
      GammaPartialProgramDefinable G (selectedRVVFTailPartialProgram hc T ρ) := by
  induction T with
  | zero A =>
    intro hA hT ρ
    apply gamma_partial_cast_target
    exact gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA
  | @step n a l A U H tail ih =>
    intro hA hT ρ
    refine ⟨gamma_selected_vf_program_tail_map hc H ρ hA hT.1,
      gamma_selected_vf_program_tail_target hc H ρ hT.2.1,?_⟩
    apply gamma_partial_cast_target
    apply gamma_partial_cast_source
    exact ih (gamma_headImage H.target hT.2.1) hT.2.2 (Fin.natAdd 1 ∘ H.selectedTailIndex ρ)

end IntegrationInACVF.Section7
