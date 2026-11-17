module

public import Integration7.GradedSemiringActionShifts
public import Mathlib.Algebra.Module.LinearMap.Defs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A shifted direct sum embeds in the original finite graded module
by retaining its literal components in the shifted degrees. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [DirectSum.GSemiring A]

def gradedShiftToSum (s : ℕ) : DirectSum ℕ (fun j => F (j+s)) →+ DirectSum ℕ F :=
  DirectSum.toAddMonoid (fun j => DirectSum.of F (j+s))

theorem graded_shift_to_sum_of (s j : ℕ) (f : F (j+s)) :
    gradedShiftToSum (F := F) s (DirectSum.of (fun j => F (j+s)) j f) = DirectSum.of F (j+s) f :=
  DirectSum.toAddMonoid_of (fun j => DirectSum.of F (j+s)) j f

def gradedShiftLinearEmbedding (B : GradedSemiringAction A F) (s : ℕ) :
    letI := gradedSemiringActionModule (B.shift s)
    letI := gradedSemiringActionModule B
    DirectSum ℕ (fun j => F (j+s)) →ₗ[DirectSum ℕ A] DirectSum ℕ F := by
  letI := gradedSemiringActionModule (B.shift s)
  letI := gradedSemiringActionModule B
  let J := gradedShiftToSum (F := F) s
  refine { toAddHom := J, map_smul' := ?_ }
  intro r f
  change J (r • f) = r • J f
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul,map_zero,zero_smul]
  | add r t hr ht => rw [add_smul,map_add,hr,ht,add_smul]
  | of i a =>
    induction f using DirectSum.induction_on with
    | zero => rw [smul_zero,map_zero,smul_zero]
    | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
    | of j f =>
      change gradedShiftToSum (F := F) s (DirectSum.of A i a • DirectSum.of (fun j => F (j+s)) j f) =
        DirectSum.of A i a • gradedShiftToSum (F := F) s (DirectSum.of (fun j => F (j+s)) j f)
      rw [graded_semiring_action_of_of (B.shift s),graded_shift_to_sum_of,
        graded_shift_to_sum_of,graded_semiring_action_of_of B]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (Nat.add_assoc i j s)
        (graded_shift_component_action_heq B s i j a f))
end IntegrationInACVF.Section7
