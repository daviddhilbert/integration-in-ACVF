module

public import Integration7.GradedSemiringActions
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-! Homogeneous additive maps commuting with actual graded actions
assemble into a linear map on finite direct sums. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F G : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [∀ j, AddCommMonoid (G j)] [DirectSum.GSemiring A]

def gradedComponentMapToSum (E : ∀ j, F j →+ G j) : DirectSum ℕ F →+ DirectSum ℕ G :=
  DirectSum.toAddMonoid (fun j => (DirectSum.of G j).comp (E j))

theorem graded_component_map_to_sum_of (E : ∀ j, F j →+ G j) (j : ℕ) (f : F j) :
    gradedComponentMapToSum E (DirectSum.of F j f) = DirectSum.of G j (E j f) :=
  DirectSum.toAddMonoid_of _ j f

def gradedSemiringActionLinearMap (B : GradedSemiringAction A F) (D : GradedSemiringAction A G)
    (E : ∀ j, F j →+ G j)
    (compat : ∀ i j (a : A i) (f : F j), E (i+j) (B.act i j a f) = D.act i j a (E j f)) :
    letI := gradedSemiringActionModule B
    letI := gradedSemiringActionModule D
    DirectSum ℕ F →ₗ[DirectSum ℕ A] DirectSum ℕ G := by
  letI := gradedSemiringActionModule B
  letI := gradedSemiringActionModule D
  let J := gradedComponentMapToSum E
  refine { toAddHom := J, map_smul' := ?_ }
  intro r f
  change J (r • f) = r • J f
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul,map_zero,zero_smul]
  | add r s hr hs => rw [add_smul,map_add,hr,hs,add_smul]
  | of i a =>
    induction f using DirectSum.induction_on with
    | zero => rw [smul_zero,map_zero,smul_zero]
    | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,smul_add]
    | of j f =>
      change gradedComponentMapToSum E (DirectSum.of A i a • DirectSum.of F j f) =
        DirectSum.of A i a • gradedComponentMapToSum E (DirectSum.of F j f)
      rw [graded_semiring_action_of_of B,graded_component_map_to_sum_of,
        graded_component_map_to_sum_of,graded_semiring_action_of_of D,compat]
end IntegrationInACVF.Section7
