import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Group.Commute.Units

/-! Homogeneous dehomogenization before groupification: additive monoid
components already suffice when the central denominator is a unit in
the target ring. This applies directly to the actual RV quotient semiring. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {A : ℕ → Type u} [∀ n, AddCommMonoid (A n)] [DirectSum.GSemiring A]
variable {T : Type v} [Ring T]

def gradedSemiringUnitComponent (g : DirectSum ℕ A →+* T) (u : Tˣ) (n : ℕ) : A n →+ T where
  toFun a := g (DirectSum.of A n a) * (↑u⁻¹ : T)^n
  map_zero' := by rw [map_zero,map_zero,zero_mul]
  map_add' a b := by rw [map_add,map_add,add_mul]

def gradedSemiringUnitNormalize (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) : DirectSum ℕ A →+* T :=
  DirectSum.toSemiring (gradedSemiringUnitComponent g u)
    (by
      change g (DirectSum.of A 0 GradedMonoid.GOne.one) * (↑u⁻¹ : T)^0 = 1
      rw [pow_zero,mul_one]
      exact g.map_one)
    (by
      intro i j a b
      change g (DirectSum.of A (i+j) (GradedMonoid.GMul.mul a b)) * (↑u⁻¹ : T)^(i+j) =
        (g (DirectSum.of A i a) * (↑u⁻¹ : T)^i) * (g (DirectSum.of A j b) * (↑u⁻¹ : T)^j)
      rw [←DirectSum.of_mul_of,map_mul,pow_add]
      have h := ((hu (DirectSum.of A j b)).units_inv_right.pow_right i).eq
      calc
        (g (DirectSum.of A i a) * g (DirectSum.of A j b)) * ((↑u⁻¹ : T)^i * (↑u⁻¹ : T)^j) =
            g (DirectSum.of A i a) * (g (DirectSum.of A j b) * (↑u⁻¹ : T)^i) * (↑u⁻¹ : T)^j := by simp only [mul_assoc]
        _ = g (DirectSum.of A i a) * ((↑u⁻¹ : T)^i * g (DirectSum.of A j b)) * (↑u⁻¹ : T)^j := by rw [h]
        _ = _ := by simp only [mul_assoc])

theorem graded_semiring_unit_normalize_of (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) (n : ℕ) (a : A n) :
    gradedSemiringUnitNormalize g u hu (DirectSum.of A n a) =
      g (DirectSum.of A n a) * (↑u⁻¹ : T)^n := DirectSum.toSemiring_of _ _ _ n a

theorem graded_semiring_unit_normalize_point (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) (j : A 1)
    (hj : g (DirectSum.of A 1 j) = (u : T)) :
    gradedSemiringUnitNormalize g u hu (DirectSum.of A 1 j) = 1 := by
  rw [graded_semiring_unit_normalize_of,hj,pow_one]
  exact u.mul_inv

end IntegrationInACVF.Section7
