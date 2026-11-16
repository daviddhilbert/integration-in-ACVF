module

public import Integration7.PointNormalizedAdditiveOperators
public import Mathlib.Algebra.DirectSum.Ring

@[expose] public section

/-! Positive homogeneous coefficient compatibility suffices for descent
when a degree-one point is normalized to one. Its products with every
coefficient still have positive degree. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A : ℕ → Type} [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]
variable {S : Type} [Ring S] (φ : DirectSum ℕ A →+* S) (p : A 1)
variable (hp : φ (DirectSum.of A 1 p)=1)
variable {M N : Type} [AddCommMonoid M] [Module (DirectSum ℕ A) M]
variable [AddCommMonoid N] [Module (DirectSum ℕ A) N]
variable (O : M →+ N)
variable (hPositive : ∀ (i : ℕ), 0<i → ∀ (a : A i) (x : M),
  O (DirectSum.of A i a • x)=DirectSum.of A i a • O x)

include hPositive in
theorem positive_operator_point_multiple (r : DirectSum ℕ A) (x : M) :
    O ((DirectSum.of A 1 p*r) • x)=(DirectSum.of A 1 p*r) • O x := by
  induction r using DirectSum.induction_on with
  | zero => rw [mul_zero,zero_smul,map_zero,zero_smul]
  | add r s hr hs => rw [mul_add,add_smul,map_add,hr,hs,add_smul]
  | of i a =>
    rw [DirectSum.of_mul_of]
    exact hPositive (1+i) (by omega) _ x

def pointNormalizedGradedOperator :
    SemimoduleScalarExtension φ M →ₗ[S] SemimoduleScalarExtension φ N :=
  pointNormalizedAdditiveOperator φ (DirectSum.of A 1 p) hp O
    (hPositive 1 (by decide) p) (positive_operator_point_multiple p O hPositive)

theorem point_normalized_graded_operator_generator (x : M) :
    pointNormalizedGradedOperator φ p hp O hPositive (scalarExtensionGenerator φ M x) =
      scalarExtensionGenerator φ N (O x) :=
  point_normalized_additive_operator_generator _ _ _ _ _ _ x

end IntegrationInACVF.Section7
