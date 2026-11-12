import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Basic

/-! Componentwise additive congruences compatible with heterogeneous products
form a congruence on the actual graded direct sum. -/

noncomputable section

namespace IntegrationInACVF.Section6.GradedCongruence

variable {A : ℕ → Type*} [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]
variable (c : ∀ i, AddCon (A i))
variable (hm : ∀ {i j} {a b : A i} {d e : A j}, c i a b → c j d e →
  c (i+j) (GradedMonoid.GMul.mul a d) (GradedMonoid.GMul.mul b e))

abbrev Component (i : ℕ) := (c i).Quotient

def product {i j} (a : Component c i) (b : Component c j) : Component c (i+j) :=
  Quotient.liftOn₂ a b (fun x y => (c (i+j)).mk' (GradedMonoid.GMul.mul x y))
    (fun _ _ _ _ hx hy => Quotient.sound (hm hx hy))

@[simp] theorem product_mk {i j} (a : A i) (b : A j) :
    product c hm ((c i).mk' a) ((c j).mk' b) =
      (c (i+j)).mk' (GradedMonoid.GMul.mul a b) := rfl

@[instance_reducible] def componentProduct : DirectSum.GNonUnitalNonAssocSemiring (Component c) where
  mul := product c hm
  mul_zero := by
    intro i j a
    induction a using (c i).induction_on with
    | H a =>
      change (c (i+j)).mk' (GradedMonoid.GMul.mul a (0 : A j)) = 0
      rw [DirectSum.GNonUnitalNonAssocSemiring.mul_zero, map_zero]
  zero_mul := by
    intro i j b
    induction b using (c j).induction_on with
    | H b =>
      change (c (i+j)).mk' (GradedMonoid.GMul.mul (0 : A i) b) = 0
      rw [DirectSum.GNonUnitalNonAssocSemiring.zero_mul, map_zero]
  mul_add := by
    intro i j a b d
    induction a using (c i).induction_on with
    | H a =>
      induction b using (c j).induction_on with
      | H b =>
        induction d using (c j).induction_on with
        | H d =>
          change (c (i+j)).mk' (GradedMonoid.GMul.mul a (b+d)) =
            (c (i+j)).mk' (GradedMonoid.GMul.mul a b) +
              (c (i+j)).mk' (GradedMonoid.GMul.mul a d)
          rw [DirectSum.GNonUnitalNonAssocSemiring.mul_add, map_add]
  add_mul := by
    intro i j a b d
    induction a using (c i).induction_on with
    | H a =>
      induction b using (c i).induction_on with
      | H b =>
        induction d using (c j).induction_on with
        | H d =>
          change (c (i+j)).mk' (GradedMonoid.GMul.mul (a+b) d) =
            (c (i+j)).mk' (GradedMonoid.GMul.mul a d) +
              (c (i+j)).mk' (GradedMonoid.GMul.mul b d)
          rw [DirectSum.GNonUnitalNonAssocSemiring.add_mul, map_add]

def projection : DirectSum ℕ A →+ DirectSum ℕ (Component c) :=
  DirectSum.map (fun i => (c i).mk')

@[simp] theorem projection_of (i : ℕ) (a : A i) :
    projection c (DirectSum.of A i a) = DirectSum.of (Component c) i ((c i).mk' a) :=
  DirectSum.map_of _ _ _

theorem projection_mul (x y : DirectSum ℕ A) :
    projection c (x*y) = (letI := componentProduct c hm; projection c x * projection c y) := by
  let := componentProduct c hm
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j b => simp only [DirectSum.of_mul_of, projection_of]; rfl
    | add y z hy hz => simp only [mul_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]

/-- Its relation is componentwise, rather than an unrestricted generated
congruence that could identify additional homogeneous classes. -/
def congruence : RingCon (DirectSum ℕ A) where
  r x y := projection c x = projection c y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  add' := by intro a b d e hab hde; simp only [map_add, hab, hde]
  mul' := by
    intro a b d e hab hde
    simp only [projection_mul c hm, hab, hde]

theorem congruence_iff (x y : DirectSum ℕ A) :
    congruence c hm x y ↔ ∀ i, c i (x i) (y i) := by
  change projection c x = projection c y ↔ _
  rw [projection, DirectSum.map_eq_iff]
  exact forall_congr' (fun i => (c i).eq)

theorem congruence_of_iff (i : ℕ) (a b : A i) :
    congruence c hm (DirectSum.of A i a) (DirectSum.of A i b) ↔ c i a b := by
  change projection c (DirectSum.of A i a) = projection c (DirectSum.of A i b) ↔ _
  rw [projection_of, projection_of, (DirectSum.of_injective i).eq_iff]
  exact (c i).eq

end IntegrationInACVF.Section6.GradedCongruence
