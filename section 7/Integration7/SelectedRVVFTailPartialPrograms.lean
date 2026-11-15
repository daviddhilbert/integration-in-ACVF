import Integration7.SelectedRVVFTailProgramSelectors
import Integration7.PartialContractionEqualityTransport

/-! Every specified ordered contraction lifts to an actual partial
contraction of the selected-label VF realization. Only the added VF tail
remains, with exactly the original retained RV selector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a l d : ℕ}

def selectedRVVFTailPartialProgram (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) :
    (ρ : Fin d → Fin a) →
      PartialContractionProgram S d (n := n)
        (nativeProgramSelectedRVVFTailLift (n := n) (d := d) hc A ρ)
        (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) := by
  induction T with
  | zero A =>
    intro ρ
    let R : PartialContractionProgram S d (n := 0)
        (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc A ρ)
        (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc A ρ) := .zero _
    exact partialCastTarget R
      (congrArg (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc A)
        (selected_vf_tail_zero_selector A ρ).symm)
  | @step n a l A U H tail ih =>
    intro ρ
    let χ := Fin.natAdd 1 ∘ H.selectedTailIndex ρ
    let R := ih χ
    let R' := partialCastSource R (H.selected_vf_program_tail_contracted_set hc ρ).symm
    let R'' := partialCastTarget R'
      (congrArg (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U)
        (selected_vf_tail_step_selector H tail ρ).symm)
    exact .step (H.selectedVFProgramTail hc ρ) R''

end IntegrationInACVF.Section7
