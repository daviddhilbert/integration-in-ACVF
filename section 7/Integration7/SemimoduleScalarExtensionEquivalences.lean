module

public import Integration7.ScalarExtensionPaddingEquivalences

@[expose] public section

/-! Linear equivalences induce genuine equivalences on the balanced
scalar extensions, with both directions computed on generators. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type z} [AddCommMonoid N] [Module R N]

def scalarExtensionLinearEquiv (e : M ≃ₗ[R] N) :
    SemimoduleScalarExtension φ M ≃ₗ[S] SemimoduleScalarExtension φ N :=
  scalarExtensionPaddingEquiv φ e.toLinearMap e.symm.toLinearMap 1 (map_one φ)
    (fun x => (e.symm_apply_apply x).trans (one_smul R x).symm)
    (fun y => (e.apply_symm_apply y).trans (one_smul R y).symm)

theorem scalar_extension_equiv_generator (e : M ≃ₗ[R] N) (x : M) :
    scalarExtensionLinearEquiv φ e (scalarExtensionGenerator φ M x) = scalarExtensionGenerator φ N (e x) :=
  scalar_extension_map_generator φ e.toLinearMap x

theorem scalar_extension_equiv_inverse_generator (e : M ≃ₗ[R] N) (y : N) :
    (scalarExtensionLinearEquiv φ e).symm (scalarExtensionGenerator φ N y) = scalarExtensionGenerator φ M (e.symm y) :=
  scalar_extension_map_generator φ e.symm.toLinearMap y
end IntegrationInACVF.Section7
