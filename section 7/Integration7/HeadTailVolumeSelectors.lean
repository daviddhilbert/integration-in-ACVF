module

public import Integration7.OrderedAppendVolumeIndices
public import IntegrationSection6.StandardProgramPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The first head tag followed by all remaining tags is precisely the
full ordered program's VF volume selector, with the recursive degree cast. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a l : ℕ}
variable {U : DefSet (M := M) S (n+1) a} {V : DefSet (M := M) S 0 l}

theorem head_tail_volume_degree (n : ℕ) : appendVolumeDegree n 0 = n := by
  rw [append_volume_degree_eq,Nat.zero_add]

theorem head_tail_append_volume_index (T : HeadPreparation U)
    (tail : OrderedContractionProgram S T.contractedSet V) (i : Fin (n+1)) :
    orderedAppendVolumeIndex (k := 0) tail (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
      (Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i) =
      (OrderedContractionProgram.step T tail).volumeIndex i := by
  cases i using Fin.cases with
  | zero =>
    have hi : Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm (0 : Fin (n+1)) =
        Fin.cast (append_volume_length_eq n 0).symm (Fin.castAdd n (0 : Fin 1)) := Fin.ext rfl
    rw [hi,ordered_append_old_index]
    rfl
  | succ j =>
    have hi : Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm j.succ =
        Fin.cast (append_volume_length_eq n 0).symm (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [Fin.coe_cast,Fin.val_succ,Fin.val_natAdd]
      omega
    rw [hi,ordered_append_vf_index]
    rfl

theorem head_tail_append_density_index (T : HeadPreparation U)
    (tail : OrderedContractionProgram S T.contractedSet V) (δ : Fin a) :
    orderedAppendDensityIndex tail (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) =
      suffixIndex (OrderedContractionProgram.step T tail).rvArity_le δ :=
  ordered_append_density_index (OrderedContractionProgram.step T tail) δ

theorem standard_from_program_volume_index {p : ℕ} {A X : DefSet (M := M) S p a}
    (σ : Equiv.Perm (Fin p)) (P : OrderedContractionProgram S X V)
    (hX : X = vfPermutationImage A σ) (i : Fin p) :
    (standardFromProgram A σ P hX).volumeIndex i = P.volumeIndex (σ.symm i) := by
  change (orderedCastSource P hX).volumeIndex (σ.symm i) = _
  rw [orderedCastSource_volumeIndex]

end IntegrationInACVF.Section7
