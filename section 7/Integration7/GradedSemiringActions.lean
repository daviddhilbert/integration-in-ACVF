module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! Assemble a graded semiring action from genuine biadditive
homogeneous actions and their unit and associativity proofs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section7
variable {A F : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [DirectSum.GSemiring A]

structure GradedSemiringAction (A F : ℕ → Type) [∀ i, AddCommMonoid (A i)]
    [∀ j, AddCommMonoid (F j)] [DirectSum.GSemiring A] where
  act : ∀ i j, A i →+ (F j →+ F (i+j))
  one_act : ∀ j (f : F j), HEq (act 0 j GradedMonoid.GOne.one f) f
  mul_act : ∀ i j k (a : A i) (b : A j) (f : F k),
    HEq (act (i+j) k (GradedMonoid.GMul.mul a b) f) (act i (j+k) a (act j k b f))

def gradedComponentActionToSum (act : ∀ i j, A i →+ (F j →+ F (i+j))) (i : ℕ) :
    A i →+ AddMonoid.End (DirectSum ℕ F) where
  toFun a := DirectSum.toAddMonoid (fun j => (DirectSum.of F (i+j)).comp (act i j a))
  map_zero' := by
    apply DirectSum.addHom_ext
    intro j f
    change DirectSum.toAddMonoid (fun j => (DirectSum.of F (i+j)).comp (act i j 0))
      (DirectSum.of F j f) = 0
    simp only [DirectSum.toAddMonoid_of,AddMonoidHom.comp_apply,map_zero,AddMonoidHom.zero_apply]
  map_add' a b := by
    apply DirectSum.addHom_ext
    intro j f
    change DirectSum.toAddMonoid (fun j => (DirectSum.of F (i+j)).comp (act i j (a+b)))
      (DirectSum.of F j f) =
      DirectSum.toAddMonoid (fun j => (DirectSum.of F (i+j)).comp (act i j a)) (DirectSum.of F j f) +
        DirectSum.toAddMonoid (fun j => (DirectSum.of F (i+j)).comp (act i j b)) (DirectSum.of F j f)
    simp only [DirectSum.toAddMonoid_of,AddMonoidHom.comp_apply,map_add,AddMonoidHom.add_apply]

theorem graded_component_action_sum_of
    (act : ∀ i j, A i →+ (F j →+ F (i+j))) (i j : ℕ) (a : A i) (f : F j) :
    gradedComponentActionToSum act i a (DirectSum.of F j f) = DirectSum.of F (i+j) (act i j a f) :=
  DirectSum.toAddMonoid_of _ j f

def gradedSemiringActionHom (B : GradedSemiringAction A F) :
    DirectSum ℕ A →+* AddMonoid.End (DirectSum ℕ F) :=
  DirectSum.toSemiring (gradedComponentActionToSum B.act) (by
    apply DirectSum.addHom_ext
    intro j f
    rw [graded_component_action_sum_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (Nat.zero_add j) (B.one_act j f))) (by
    intro i j a b
    apply DirectSum.addHom_ext
    intro k f
    change gradedComponentActionToSum B.act (i+j) (GradedMonoid.GMul.mul a b) (DirectSum.of F k f) =
      gradedComponentActionToSum B.act i a (gradedComponentActionToSum B.act j b (DirectSum.of F k f))
    rw [graded_component_action_sum_of,graded_component_action_sum_of,graded_component_action_sum_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (Nat.add_assoc i j k) (B.mul_act i j k a b f)))

def gradedSemiringActionModule (B : GradedSemiringAction A F) : Module (DirectSum ℕ A) (DirectSum ℕ F) where
  smul a f := gradedSemiringActionHom B a f
  one_smul f := by
    change gradedSemiringActionHom B 1 f=f
    rw [map_one]
    rfl
  mul_smul a b f := by
    change gradedSemiringActionHom B (a*b) f=gradedSemiringActionHom B a (gradedSemiringActionHom B b f)
    rw [map_mul]
    rfl
  zero_smul f := by
    change gradedSemiringActionHom B 0 f=0
    rw [map_zero]
    rfl
  smul_zero a := (gradedSemiringActionHom B a).map_zero
  smul_add a f g := (gradedSemiringActionHom B a).map_add f g
  add_smul a b f := by
    change gradedSemiringActionHom B (a+b) f=gradedSemiringActionHom B a f+gradedSemiringActionHom B b f
    rw [map_add]
    rfl

theorem graded_semiring_action_of_of (B : GradedSemiringAction A F) (i j : ℕ) (a : A i) (f : F j) :
    letI := gradedSemiringActionModule B
    DirectSum.of A i a • DirectSum.of F j f = DirectSum.of F (i+j) (B.act i j a f) := by
  change gradedSemiringActionHom B (DirectSum.of A i a) (DirectSum.of F j f) = _
  rw [gradedSemiringActionHom,DirectSum.toSemiring_of,graded_component_action_sum_of]

end IntegrationInACVF.Section7
