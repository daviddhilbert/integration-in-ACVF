module

public import Integration7.SelectedRVVFTailProgramHeads
public import IntegrationSection5.OrderedContractionProgram

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Retained selected labels shift through a head step by the same
literal suffix selector as in the original ordered program. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a l d : ℕ}

theorem selected_vf_tail_zero_selector (A : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) :
    suffixIndex (OrderedContractionProgram.zero A).rvArity_le ∘ ρ = ρ := by
  funext j
  apply Fin.ext
  simp [suffixIndex]

theorem selected_vf_tail_step_selector {A : DefSet (M := M) S (n+1) a} {U : DefSet (M := M) S 0 l}
    (T : HeadPreparation A) (tail : OrderedContractionProgram S T.contractedSet U) (ρ : Fin d → Fin a) :
    suffixIndex (OrderedContractionProgram.step T tail).rvArity_le ∘ ρ =
      suffixIndex tail.rvArity_le ∘ (Fin.natAdd 1 ∘ T.selectedTailIndex ρ) := by
  funext j
  apply Fin.ext
  have hT := specialRelative_rvArity_le T.special
  have ht := tail.rvArity_le
  change 1+T.arity ≤ l at ht
  change l-a+(ρ j).val = l-(1+T.arity)+(1+(T.arity-a+(ρ j).val))
  omega

end IntegrationInACVF.Section7
