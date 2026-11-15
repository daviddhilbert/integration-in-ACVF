import Integration7.GradedPointPadding
import Integration7.ScalarExtensionPaddingEquivalences

/-! When the central point coefficient becomes one, positive shifted
functions and full finite graded functions have isomorphic scalar extensions. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [DirectSum.GSemiring A] {S : Type} [Ring S]

def gradedPointNormalizationEquiv (φ : DirectSum ℕ A →+* S)
    (B : GradedSemiringAction A F) (a : A 1)
    (ha : ∀ r : DirectSum ℕ A, Commute r (DirectSum.of A 1 a))
    (hφ : φ (DirectSum.of A 1 a)=1) :
    letI := gradedSemiringActionModule B
    letI := gradedSemiringActionModule (B.shift 1)
    SemimoduleScalarExtension φ (DirectSum ℕ (fun j => F (j+1))) ≃ₗ[S]
      SemimoduleScalarExtension φ (DirectSum ℕ F) := by
  letI := gradedSemiringActionModule B
  letI := gradedSemiringActionModule (B.shift 1)
  let I := gradedShiftLinearEmbedding B 1
  let P := gradedPointPaddingLinearMap B a ha
  have hIP (f : DirectSum ℕ F) : I (P f)=DirectSum.of A 1 a • f :=
    graded_point_padding_embedding B a f
  have hPI (g : DirectSum ℕ (fun j => F (j+1))) : P (I g)=DirectSum.of A 1 a • g := by
    apply graded_shift_to_sum_injective (F := F) 1
    change I (P (I g)) = I (DirectSum.of A 1 a • g)
    rw [hIP,I.map_smul]
  exact scalarExtensionPaddingEquiv φ I P (DirectSum.of A 1 a) hφ hPI hIP
end IntegrationInACVF.Section7
