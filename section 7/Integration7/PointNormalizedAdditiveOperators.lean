module

public import Integration7.SemimoduleScalarExtensionMaps

@[expose] public section

/-! Additive operators descend after point normalization when they
commute with the point and its multiples. No injectivity of point
multiplication, or cancellation before normalization, is used. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) (P : R) (hP : φ P=1)
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type z} [AddCommMonoid N] [Module R N]
variable (O : M →+ N)
variable (hPoint : ∀ x, O (P • x)=P • O x)
variable (hMultiple : ∀ r x, O ((P*r) • x)=(P*r) • O x)

include P hP hPoint hMultiple

theorem point_normalized_operator_generators_smul (r : R) (x : M) :
    scalarExtensionGenerator φ N (O (r • x)) =
      φ r • scalarExtensionGenerator φ N (O x) := by
  calc
    scalarExtensionGenerator φ N (O (r • x)) =
        scalarExtensionGenerator φ N (P • O (r • x)) := by
      rw [scalar_extension_generator_smul,hP,one_smul]
    _ = scalarExtensionGenerator φ N (O (P • (r • x))) := congrArg _ (hPoint (r • x)).symm
    _ = scalarExtensionGenerator φ N (O ((P*r) • x)) := by rw [mul_smul]
    _ = scalarExtensionGenerator φ N ((P*r) • O x) := congrArg _ (hMultiple r x)
    _ = φ r • scalarExtensionGenerator φ N (O x) := by
      rw [scalar_extension_generator_smul,map_mul,hP,one_mul]

def pointNormalizedAdditiveOperator : SemimoduleScalarExtension φ M →ₗ[S] SemimoduleScalarExtension φ N :=
  scalarExtensionLift φ ((scalarExtensionGeneratorHom φ N).comp O)
    (point_normalized_operator_generators_smul φ P hP O hPoint hMultiple)

theorem point_normalized_additive_operator_generator (x : M) :
    pointNormalizedAdditiveOperator φ P hP O hPoint hMultiple (scalarExtensionGenerator φ M x) =
      scalarExtensionGenerator φ N (O x) :=
  scalar_extension_lift_generator _ _ _ x

end IntegrationInACVF.Section7
