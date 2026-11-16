module

public import Mathlib.Algebra.Module.Presentation.Basic

@[expose] public section

/-! Scalar extension from a possibly noncommutative semiring to a ring.
The target-module presentation uses the checked Mathlib Relations API.
Its generators are the source semimodule elements, with the actual zero,
addition and scalar-balancing relations. Commutativity is not assumed. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v w z
variable {R : Type u} [Semiring R] {S : Type v} [Ring S]
variable (φ : R →+* S) (M : Type w) [AddCommMonoid M] [Module R M]

abbrev semimoduleScalarExtensionRelations : Module.Relations S where
  G := M
  R := Unit ⊕ ((M × M) ⊕ (R × M))
  relation
    | .inl _ => Finsupp.single 0 1
    | .inr (.inl (x,y)) => Finsupp.single (x+y) 1 - Finsupp.single x 1 - Finsupp.single y 1
    | .inr (.inr (r,x)) => Finsupp.single (r • x) 1 - Finsupp.single x (φ r)

abbrev SemimoduleScalarExtension := (semimoduleScalarExtensionRelations φ M).Quotient

def scalarExtensionGenerator (x : M) : SemimoduleScalarExtension φ M :=
  (semimoduleScalarExtensionRelations φ M).toQuotient (Finsupp.single x 1)

theorem scalar_extension_generator_zero : scalarExtensionGenerator φ M 0 = 0 :=
  (semimoduleScalarExtensionRelations φ M).toQuotient_relation (.inl ())

theorem scalar_extension_generator_add (x y : M) :
    scalarExtensionGenerator φ M (x+y) = scalarExtensionGenerator φ M x + scalarExtensionGenerator φ M y := by
  have h := (semimoduleScalarExtensionRelations φ M).toQuotient_relation (.inr (.inl (x,y)))
  change (semimoduleScalarExtensionRelations φ M).toQuotient
    (Finsupp.single (x+y) 1 - Finsupp.single x 1 - Finsupp.single y 1) = 0 at h
  rw [map_sub,map_sub,sub_sub] at h
  exact sub_eq_zero.mp h

theorem scalar_extension_generator_smul (r : R) (x : M) :
    scalarExtensionGenerator φ M (r • x) = φ r • scalarExtensionGenerator φ M x := by
  have h := (semimoduleScalarExtensionRelations φ M).toQuotient_relation (.inr (.inr (r,x)))
  change (semimoduleScalarExtensionRelations φ M).toQuotient
    (Finsupp.single (r • x) 1 - Finsupp.single x (φ r)) = 0 at h
  have hSingle : Finsupp.single x (φ r) = φ r • Finsupp.single x (1 : S) := by
    simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
  rw [map_sub,hSingle,map_smul] at h
  exact sub_eq_zero.mp h

def scalarExtensionGeneratorHom : M →+ SemimoduleScalarExtension φ M where
  toFun := scalarExtensionGenerator φ M
  map_zero' := scalar_extension_generator_zero φ M
  map_add' := scalar_extension_generator_add φ M

variable {M} {N : Type z} [AddCommGroup N] [Module S N]

def scalarExtensionSolution (f : M →+ N) (hf : ∀ r x, f (r • x) = φ r • f x) :
    (semimoduleScalarExtensionRelations φ M).Solution N where
  var := f
  linearCombination_var_relation := by
    rintro (_ | (⟨x,y⟩ | ⟨r,x⟩))
    · simp [semimoduleScalarExtensionRelations]
    · simp [semimoduleScalarExtensionRelations,map_sub,map_add,sub_sub]
    · simp [semimoduleScalarExtensionRelations,hf]

def scalarExtensionLift (f : M →+ N) (hf : ∀ r x, f (r • x) = φ r • f x) :
    SemimoduleScalarExtension φ M →ₗ[S] N := (scalarExtensionSolution φ f hf).fromQuotient

theorem scalar_extension_lift_generator (f : M →+ N) (hf : ∀ r x, f (r • x) = φ r • f x) (x : M) :
    scalarExtensionLift φ f hf (scalarExtensionGenerator φ M x) = f x := by
  change (scalarExtensionSolution φ f hf).fromQuotient
    ((semimoduleScalarExtensionRelations φ M).toQuotient (Finsupp.single x 1)) = f x
  rw [Module.Relations.Solution.fromQuotient_toQuotient,Module.Relations.Solution.π_single]
  rfl

theorem scalar_extension_linearMap_ext
    {f g : SemimoduleScalarExtension φ M →ₗ[S] N}
    (h : ∀ x, f (scalarExtensionGenerator φ M x) = g (scalarExtensionGenerator φ M x)) : f = g :=
  Module.Relations.Quotient.linearMap_ext h

theorem scalar_extension_lift_unique (f : M →+ N) (hf : ∀ r x, f (r • x) = φ r • f x)
    (g : SemimoduleScalarExtension φ M →ₗ[S] N)
    (hg : ∀ x, g (scalarExtensionGenerator φ M x) = f x) : g = scalarExtensionLift φ f hf := by
  apply scalar_extension_linearMap_ext φ
  intro x
  exact (hg x).trans (scalar_extension_lift_generator φ f hf x).symm

end IntegrationInACVF.Section7
