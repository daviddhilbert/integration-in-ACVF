module

public import Integration7.SemimoduleScalarExtensionMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Linear functionals extend through the actual balanced scalar
extension, naturally with respect to genuine semimodule maps. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type z} [AddCommMonoid N] [Module R N]

def scalarExtensionFunctional (I : M →ₗ[R] R) : SemimoduleScalarExtension φ M →ₗ[S] S :=
  scalarExtensionLift φ (φ.toAddMonoidHom.comp I.toAddMonoidHom) (by
    intro r x
    change φ (I (r • x))=φ r • φ (I x)
    rw [I.map_smul,smul_eq_mul,map_mul,smul_eq_mul])

theorem scalar_extension_functional_generator (I : M →ₗ[R] R) (x : M) :
    scalarExtensionFunctional φ I (scalarExtensionGenerator φ M x)=φ (I x) :=
  scalar_extension_lift_generator φ _ _ x

theorem scalar_extension_functional_natural (I : M →ₗ[R] R) (f : N →ₗ[R] M) :
    (scalarExtensionFunctional φ I).comp (scalarExtensionMap φ f)=scalarExtensionFunctional φ (I.comp f) := by
  apply scalar_extension_linearMap_ext φ
  intro x
  simp only [LinearMap.comp_apply,scalar_extension_map_generator,scalar_extension_functional_generator]
end IntegrationInACVF.Section7
