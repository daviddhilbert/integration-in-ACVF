module

public import Integration7.HeadTailVolumeSelectors

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal selectors when a prescribed ordered tail follows the chosen head. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a l : ℕ} {A : DefSet (M := M) S (n+1) a} {V : DefSet (M := M) S 0 l}

def standardPrependHead (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ))
    (tail : OrderedContractionProgram S T.contractedSet V) : StandardContraction A σ :=
  ⟨l,V,.step T tail⟩

theorem standard_prepend_head_volume_head (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ))
    (tail : OrderedContractionProgram S T.contractedSet V) :
    (standardPrependHead σ T tail).volumeIndex (σ 0) = suffixIndex tail.rvArity_le 0 := by
  change (OrderedContractionProgram.step T tail).volumeIndex (σ.symm (σ 0)) = _
  rw [σ.symm_apply_apply]
  rfl

theorem standard_prepend_head_volume_tail (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ))
    (tail : OrderedContractionProgram S T.contractedSet V) (j : Fin n) :
    (standardPrependHead σ T tail).volumeIndex (σ j.succ) = tail.volumeIndex j := by
  change (OrderedContractionProgram.step T tail).volumeIndex (σ.symm (σ j.succ)) = _
  rw [σ.symm_apply_apply]
  rfl

theorem standard_prepend_head_old_index (σ : Equiv.Perm (Fin (n+1)))
    (T : HeadPreparation (vfPermutationImage A σ))
    (tail : OrderedContractionProgram S T.contractedSet V) (δ : Fin a) :
    suffixIndex tail.rvArity_le (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) =
      suffixIndex (standardPrependHead σ T tail).program.rvArity_le δ := by
  apply Fin.ext
  have ht := tail.rvArity_le
  have hT := specialRelative_rvArity_le T.special
  change l-(1+T.arity)+(1+(T.arity-a+δ.val)) = l-a+δ.val
  omega

end IntegrationInACVF.Section7
