module

public import Integration7.SelectedRVVFTailPartialPrograms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The lifted specified program has exactly the original new-VF
volume selectors and exactly the original retained-label selectors. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a l d : ℕ}

theorem selected_rv_vf_tail_partial_volume_index
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) : ∀ ρ : Fin d → Fin a,
      (selectedRVVFTailPartialProgram hc T ρ).volumeIndex = T.volumeIndex := by
  induction T with
  | zero A => intro ρ; funext i; exact i.elim0
  | @step n a l A U H tail ih =>
    intro ρ
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (partialCastTarget
        (partialCastSource (selectedRVVFTailPartialProgram hc tail (Fin.natAdd 1 ∘ H.selectedTailIndex ρ)) _)
          _).volumeIndex i = tail.volumeIndex i
      rw [partial_cast_target_volume_index,partial_cast_source_volume_index]
      exact congrFun (ih (Fin.natAdd 1 ∘ H.selectedTailIndex ρ)) i

theorem selected_rv_vf_tail_partial_old_label_index
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S A U) (ρ : Fin d → Fin a) (δ : Fin a) :
    suffixIndex (selectedRVVFTailPartialProgram hc T ρ).rvArity_le δ = suffixIndex T.rvArity_le δ := rfl

end IntegrationInACVF.Section7
