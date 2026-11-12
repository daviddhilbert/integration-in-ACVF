import Mathlib.GroupTheory.Congruence.Basic

/-!
# The additive quotient inversion used in Proposition 6.18

The actual lifting map and its exact kernel description must be supplied by
the geometric results. This module proves the additive quotient argument,
including the representative characterization and uniqueness.
-/

namespace IntegrationInACVF.Section6

noncomputable section

variable {A B : Type*} [AddMonoid A] [AddMonoid B]

/-- The induced additive map from a quotient by the exact kernel of lifting. -/
def quotientLift (c : AddCon A) (L : A →+ B)
    (hkernel : ∀ a b, c a b ↔ L a = L b) : c.Quotient →+ B :=
  c.lift L (fun a b h => (hkernel a b).mp h)

theorem quotientLift_bijective (c : AddCon A) (L : A →+ B)
    (hsurj : Function.Surjective L) (hkernel : ∀ a b, c a b ↔ L a = L b) :
    Function.Bijective (quotientLift c L hkernel) := by
  constructor
  · intro q r
    induction q using c.induction_on with
    | H a =>
      induction r using c.induction_on with
      | H b =>
        intro he
        exact Quotient.sound ((hkernel a b).mpr he)
  · intro b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨c.mk' a, ha⟩

/-- Canonical additive integration, inverse to a surjective additive lift
whose kernel is precisely the specified congruence. -/
def quotientIntegration (c : AddCon A) (L : A →+ B)
    (hsurj : Function.Surjective L) (hkernel : ∀ a b, c a b ↔ L a = L b) :
    B ≃+ c.Quotient :=
  (AddEquiv.ofBijective (quotientLift c L hkernel)
    (quotientLift_bijective c L hsurj hkernel)).symm

/-- The representative characterization in Proposition 6.18. -/
theorem quotientIntegration_eq_iff (c : AddCon A) (L : A →+ B)
    (hsurj : Function.Surjective L) (hkernel : ∀ a b, c a b ↔ L a = L b)
    (b : B) (a : A) : quotientIntegration c L hsurj hkernel b = c.mk' a ↔ b = L a := by
  exact (AddEquiv.ofBijective (quotientLift c L hkernel)
    (quotientLift_bijective c L hsurj hkernel)).symm_apply_eq

@[simp] theorem quotientIntegration_lift (c : AddCon A) (L : A →+ B)
    (hsurj : Function.Surjective L) (hkernel : ∀ a b, c a b ↔ L a = L b) (a : A) :
    quotientIntegration c L hsurj hkernel (L a) = c.mk' a :=
  (quotientIntegration_eq_iff c L hsurj hkernel (L a) a).mpr rfl

/-- The characterization determines integration uniquely on every VF class. -/
theorem quotientIntegration_unique (c : AddCon A) (L : A →+ B)
    (hsurj : Function.Surjective L) (hkernel : ∀ a b, c a b ↔ L a = L b)
    (f : B → c.Quotient) (hf : ∀ a, f (L a) = c.mk' a) :
    f = quotientIntegration c L hsurj hkernel := by
  funext b
  obtain ⟨a, rfl⟩ := hsurj b
  exact (hf a).trans (quotientIntegration_lift c L hsurj hkernel a).symm

end

end IntegrationInACVF.Section6
