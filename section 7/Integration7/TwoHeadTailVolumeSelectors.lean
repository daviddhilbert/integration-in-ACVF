module

public import Integration7.HeadTailVolumeSelectors
public import IntegrationSection6.VFPrefixSwaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The positive tuple consisting of the first two contracted VF tags
and all subsequently appended tags is the full ordered volume tuple.
Exchanging its first two entries commutes with appending every tail tag. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a l : ℕ}
variable {U : DefSet (M := M) S (n+2) a} {V : DefSet (M := M) S 0 l}

def twoHeadPartialProgram (T : HeadPreparation U) (T₂ : HeadPreparation T.contractedSet) :
    PartialContractionProgram S n (n := 2) U T₂.contractedSet :=
  .step T (.step T₂ (.zero _))

theorem two_head_tail_volume_degree (n : ℕ) : appendVolumeDegree n 1 = n+1 := by
  rw [append_volume_degree_eq]
  omega

theorem two_head_tail_append_volume_index (T : HeadPreparation U) (T₂ : HeadPreparation T.contractedSet)
    (tail : OrderedContractionProgram S T₂.contractedSet V) (i : Fin (n+2)) :
    orderedAppendVolumeIndex (k := 1) tail (twoHeadPartialProgram T T₂).volumeIndex
      (Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm i) =
      (OrderedContractionProgram.step T (.step T₂ tail)).volumeIndex i := by
  cases i using Fin.cases with
  | zero =>
    have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm (0 : Fin (n+2)) =
        Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (0 : Fin 2)) := Fin.ext rfl
    rw [hi,ordered_append_old_index]
    apply Fin.ext
    have h₂ := specialRelative_rvArity_le T₂.special
    have ht := tail.rvArity_le
    change l-(1+T₂.arity)+((1+T₂.arity)-(1+T.arity)+0) = l-(1+T.arity)+0
    omega
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm
          (0 : Fin (n+1)).succ =
          Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (1 : Fin 2)) := Fin.ext rfl
      rw [hi,ordered_append_old_index]
      apply Fin.ext
      change l-(1+T₂.arity)+((1+T₂.arity)-(1+T₂.arity)+0) = l-(1+T₂.arity)+0
      omega
    | succ j =>
      have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm j.succ.succ =
          Fin.cast (append_volume_length_eq n 1).symm (Fin.natAdd 2 j) := by
        apply Fin.ext
        simp only [Fin.coe_cast,Fin.val_succ,Fin.val_natAdd]
        omega
      rw [hi,ordered_append_vf_index]
      rfl

theorem two_head_tail_append_swapped_volume_index (T : HeadPreparation U) (T₂ : HeadPreparation T.contractedSet)
    (tail : OrderedContractionProgram S T₂.contractedSet V) (i : Fin (n+2)) :
    orderedAppendVolumeIndex (k := 1) tail ((twoHeadPartialProgram T T₂).volumeIndex ∘ swapTwo.symm)
      (Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm i) =
      (OrderedContractionProgram.step T (.step T₂ tail)).volumeIndex (swapFirstTwo n i) := by
  cases i using Fin.cases with
  | zero =>
    rw [swapFirstTwo_zero]
    have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm (0 : Fin (n+2)) =
        Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (0 : Fin 2)) := Fin.ext rfl
    rw [hi,ordered_append_old_index]
    have h := two_head_tail_append_volume_index T T₂ tail (0 : Fin (n+1)).succ
    have hj : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm (0 : Fin (n+1)).succ =
        Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (1 : Fin 2)) := Fin.ext rfl
    rw [hj,ordered_append_old_index] at h
    exact h
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      rw [swapFirstTwo_one]
      have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm (0 : Fin (n+1)).succ =
          Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (1 : Fin 2)) := Fin.ext rfl
      rw [hi,ordered_append_old_index]
      have h := two_head_tail_append_volume_index T T₂ tail 0
      have hj : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm (0 : Fin (n+2)) =
          Fin.cast (append_volume_length_eq n 1).symm (Fin.castAdd n (0 : Fin 2)) := Fin.ext rfl
      rw [hj,ordered_append_old_index] at h
      exact h
    | succ j =>
      rw [swapFirstTwo_tail]
      have hi : Fin.cast (congrArg Nat.succ (two_head_tail_volume_degree n)).symm j.succ.succ =
          Fin.cast (append_volume_length_eq n 1).symm (Fin.natAdd 2 j) := by
        apply Fin.ext
        simp only [Fin.coe_cast,Fin.val_succ,Fin.val_natAdd]
        omega
      rw [hi,ordered_append_vf_index]
      rfl

theorem two_head_tail_append_density_index (T : HeadPreparation U) (T₂ : HeadPreparation T.contractedSet)
    (tail : OrderedContractionProgram S T₂.contractedSet V) (δ : Fin a) :
    orderedAppendDensityIndex tail (suffixIndex (twoHeadPartialProgram T T₂).rvArity_le δ) =
      suffixIndex (OrderedContractionProgram.step T (.step T₂ tail)).rvArity_le δ := by
  rw [ordered_append_density_index]
  apply Fin.ext
  have h₁ := specialRelative_rvArity_le T.special
  have h₂ := specialRelative_rvArity_le T₂.special
  have ht := tail.rvArity_le
  change l-(1+T₂.arity)+((1+T₂.arity)-a+δ.val) = l-a+δ.val
  omega

end IntegrationInACVF.Section7
