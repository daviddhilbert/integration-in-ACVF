import Integration7.SemimoduleScalarExtensionMaps

/-! Two maps whose composites multiply by a scalar become inverse
after a scalar extension sending that scalar to one. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type z} [AddCommMonoid N] [Module R N]

theorem scalar_extension_padding_comp (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (r : R) (hr : φ r=1) (h : ∀ x, g (f x)=r • x) :
    (scalarExtensionMap φ g).comp (scalarExtensionMap φ f) = LinearMap.id := by
  apply scalar_extension_linearMap_ext φ
  intro x
  change scalarExtensionMap φ g (scalarExtensionMap φ f (scalarExtensionGenerator φ M x)) =
    scalarExtensionGenerator φ M x
  rw [scalar_extension_map_generator,scalar_extension_map_generator,h,
    scalar_extension_generator_smul,hr,one_smul]

def scalarExtensionPaddingEquiv (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (r : R) (hr : φ r=1) (hM : ∀ x, g (f x)=r • x) (hN : ∀ y, f (g y)=r • y) :
    SemimoduleScalarExtension φ M ≃ₗ[S] SemimoduleScalarExtension φ N :=
  { scalarExtensionMap φ f with
    invFun := scalarExtensionMap φ g
    left_inv := fun x => congrArg (fun I => I x) (scalar_extension_padding_comp φ f g r hr hM)
    right_inv := fun y => congrArg (fun I => I y) (scalar_extension_padding_comp φ g f r hr hN) }
end IntegrationInACVF.Section7
