module

public import Integration7.SemimoduleScalarExtension

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual semimodule maps extend to the balanced scalar extension.
Their identity, composition and generator formulas hold without assuming
commutativity of the original coefficient semiring. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z q
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type z} [AddCommMonoid N] [Module R N]
variable {P : Type q} [AddCommMonoid P] [Module R P]

def scalarExtensionMap (f : M →ₗ[R] N) :
    SemimoduleScalarExtension φ M →ₗ[S] SemimoduleScalarExtension φ N :=
  scalarExtensionLift φ ((scalarExtensionGeneratorHom φ N).comp f.toAddMonoidHom) (by
    intro r x
    change scalarExtensionGenerator φ N (f (r • x)) = _
    rw [f.map_smul,scalar_extension_generator_smul]
    rfl)

theorem scalar_extension_map_generator (f : M →ₗ[R] N) (x : M) :
    scalarExtensionMap φ f (scalarExtensionGenerator φ M x) = scalarExtensionGenerator φ N (f x) :=
  scalar_extension_lift_generator φ _ _ x

theorem scalar_extension_map_id :
    scalarExtensionMap φ (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  apply scalar_extension_linearMap_ext φ
  intro x
  exact scalar_extension_map_generator φ _ x

theorem scalar_extension_map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    scalarExtensionMap φ (g.comp f) = (scalarExtensionMap φ g).comp (scalarExtensionMap φ f) := by
  apply scalar_extension_linearMap_ext φ
  intro x
  simp only [LinearMap.comp_apply,scalar_extension_map_generator]
end IntegrationInACVF.Section7
