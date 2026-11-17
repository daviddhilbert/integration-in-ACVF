module

public import Integration7.GradedShiftComponents
public import Integration7.GradedSemiringActionLinearMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A central coefficient of degree one pads every finite graded
function into positive degrees. Its literal inclusion is multiplication
by that coefficient, which also proves linearity of the padding map. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [DirectSum.GSemiring A]

def gradedPointPaddingAddHom (B : GradedSemiringAction A F) (a : A 1) :
    DirectSum ℕ F →+ DirectSum ℕ (fun j => F (j+1)) :=
  gradedComponentMapToSum (fun j =>
    (gradedDegreeAddEquiv (F := F) (Nat.add_comm 1 j)).toAddMonoidHom.comp (B.act 1 j a))

theorem graded_point_padding_embedding (B : GradedSemiringAction A F) (a : A 1)
    (f : DirectSum ℕ F) :
    letI := gradedSemiringActionModule B
    gradedShiftToSum (F := F) 1 (gradedPointPaddingAddHom B a f) = DirectSum.of A 1 a • f := by
  letI := gradedSemiringActionModule B
  induction f using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero,smul_zero]
  | add f g hf hg => rw [map_add,map_add,hf,hg,smul_add]
  | of j f =>
    change gradedShiftToSum (F := F) 1
      (gradedComponentMapToSum (fun j =>
        (gradedDegreeAddEquiv (F := F) (Nat.add_comm 1 j)).toAddMonoidHom.comp (B.act 1 j a))
          (DirectSum.of F j f)) = _
    rw [graded_component_map_to_sum_of]
    change gradedShiftToSum (F := F) 1 (DirectSum.of (fun j => F (j+1)) j
      (gradedDegreeAddEquiv (Nat.add_comm 1 j) (B.act 1 j a f))) = _
    rw [graded_shift_to_sum_of,graded_semiring_action_of_of B]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (Nat.add_comm j 1)
      (graded_degree_add_equiv_heq (Nat.add_comm 1 j) _))

def gradedPointPaddingLinearMap (B : GradedSemiringAction A F) (a : A 1)
    (ha : ∀ r : DirectSum ℕ A, Commute r (DirectSum.of A 1 a)) :
    letI := gradedSemiringActionModule B
    letI := gradedSemiringActionModule (B.shift 1)
    DirectSum ℕ F →ₗ[DirectSum ℕ A] DirectSum ℕ (fun j => F (j+1)) := by
  letI := gradedSemiringActionModule B
  letI := gradedSemiringActionModule (B.shift 1)
  refine { toAddHom := gradedPointPaddingAddHom B a, map_smul' := ?_ }
  intro r f
  apply graded_shift_to_sum_injective (F := F) 1
  change gradedShiftToSum (F := F) 1 (gradedPointPaddingAddHom B a (r • f)) =
    gradedShiftLinearEmbedding B 1 (r • gradedPointPaddingAddHom B a f)
  rw [graded_point_padding_embedding,(gradedShiftLinearEmbedding B 1).map_smul]
  change DirectSum.of A 1 a • (r • f) =
    r • gradedShiftToSum (F := F) 1 (gradedPointPaddingAddHom B a f)
  rw [graded_point_padding_embedding,smul_smul,smul_smul]
  exact congrArg (fun q : DirectSum ℕ A => q • f) (ha r).symm
end IntegrationInACVF.Section7
