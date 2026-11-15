import Integration7.PartialOrderedContractionAppending

/-! A full program obtained by appending a tail retains the original
partial volume block, followed by the tail's own VF volume block. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n a b l : ℕ}

theorem append_partial_ordered_old_volume_index
    {A : DefSet (M := M) S (p+n) a} {B : DefSet (M := M) S p b} {U : DefSet (M := M) S 0 l}
    (T : PartialContractionProgram S p (n := n) A B) :
    ∀ (E : OrderedContractionProgram S B U) (i : Fin n),
      (appendPartialOrderedProgram T E).volumeIndex (finCongr (Nat.add_comm n p) (Fin.castAdd p i)) =
        suffixIndex E.rvArity_le (T.volumeIndex i) := by
  induction T with
  | zero A => intro E i; exact i.elim0
  | @step n a b A B H tail ih =>
    intro E i
    cases i using Fin.cases with
    | zero =>
      have hi : finCongr (Nat.add_comm (n+1) p) (Fin.castAdd p (0 : Fin (n+1))) =
          (0 : Fin ((p+n)+1)) := Fin.ext rfl
      rw [hi]
      apply Fin.ext
      have ht := tail.rvArity_le
      have he := E.rvArity_le
      change 1+H.arity ≤ b at ht
      change l-(1+H.arity)+0 = l-b+(b-(1+H.arity)+0)
      omega
    | succ i =>
      have hi : finCongr (Nat.add_comm (n+1) p) (Fin.castAdd p i.succ) =
          (finCongr (Nat.add_comm n p) (Fin.castAdd p i)).succ := Fin.ext rfl
      rw [hi]
      exact ih E i

theorem append_partial_ordered_tail_volume_index
    {A : DefSet (M := M) S (p+n) a} {B : DefSet (M := M) S p b} {U : DefSet (M := M) S 0 l}
    (T : PartialContractionProgram S p (n := n) A B) :
    ∀ (E : OrderedContractionProgram S B U) (j : Fin p),
      (appendPartialOrderedProgram T E).volumeIndex (finCongr (Nat.add_comm n p) (Fin.natAdd n j)) =
        E.volumeIndex j := by
  induction T with
  | zero A =>
    intro E j
    have he : finCongr (Nat.add_comm 0 p) (Fin.natAdd 0 j) = j :=
      Fin.ext (by simp only [finCongr_apply_coe,Fin.val_natAdd,Nat.zero_add])
    rw [he]
    rfl
  | @step n a b A B H tail ih =>
    intro E j
    have hi : finCongr (Nat.add_comm (n+1) p) (Fin.natAdd (n+1) j) =
        (finCongr (Nat.add_comm n p) (Fin.natAdd n j)).succ := by
      apply Fin.ext
      simp only [finCongr_apply_coe,Fin.val_natAdd,Fin.val_succ]
      omega
    rw [hi]
    exact ih E j

end IntegrationInACVF.Section7
