import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Commute.Units

/-! Dehomogenization in a possibly noncommutative graded ring, when the
denominator is a central unit in the target. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {A : ℕ → Type u} [∀ n, AddCommGroup (A n)] [DirectSum.GRing A]
variable {T : Type v} [Ring T]

def gradedUnitComponent (g : DirectSum ℕ A →+* T) (u : Tˣ) (n : ℕ) : A n →+ T where
  toFun a := g (DirectSum.of A n a) * (↑u⁻¹ : T) ^ n
  map_zero' := by rw [map_zero,map_zero,zero_mul]
  map_add' a b := by rw [map_add,map_add,add_mul]

def gradedUnitNormalize (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) : DirectSum ℕ A →+* T :=
  DirectSum.toSemiring (gradedUnitComponent g u)
    (by
      change g (DirectSum.of A 0 GradedMonoid.GOne.one) * (↑u⁻¹ : T) ^ 0 = 1
      rw [pow_zero,mul_one]
      exact g.map_one)
    (by
      intro i j a b
      change g (DirectSum.of A (i+j) (GradedMonoid.GMul.mul a b)) * (↑u⁻¹ : T) ^ (i+j) =
        (g (DirectSum.of A i a) * (↑u⁻¹ : T) ^ i) * (g (DirectSum.of A j b) * (↑u⁻¹ : T) ^ j)
      rw [← DirectSum.of_mul_of,map_mul,pow_add]
      have h := ((hu (DirectSum.of A j b)).units_inv_right.pow_right i).eq
      calc
        (g (DirectSum.of A i a) * g (DirectSum.of A j b)) * ((↑u⁻¹ : T)^i * (↑u⁻¹ : T)^j) =
            g (DirectSum.of A i a) * (g (DirectSum.of A j b) * (↑u⁻¹ : T)^i) * (↑u⁻¹ : T)^j := by simp only [mul_assoc]
        _ = g (DirectSum.of A i a) * ((↑u⁻¹ : T)^i * g (DirectSum.of A j b)) * (↑u⁻¹ : T)^j := by rw [h]
        _ = _ := by simp only [mul_assoc])

@[simp] theorem gradedUnitNormalize_of (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) (n : ℕ) (a : A n) :
    gradedUnitNormalize g u hu (DirectSum.of A n a) = g (DirectSum.of A n a) * (↑u⁻¹ : T)^n :=
  DirectSum.toSemiring_of _ _ _ n a

theorem gradedUnitNormalize_point (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) (j : A 1)
    (hj : g (DirectSum.of A 1 j) = (u : T)) :
    gradedUnitNormalize g u hu (DirectSum.of A 1 j) = 1 := by
  rw [gradedUnitNormalize_of,hj,pow_one]
  exact u.mul_inv

abbrev GradedUnitZeroRing (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) := (gradedUnitNormalize g u hu).range

def gradedUnitZeroMap (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) : DirectSum ℕ A →+* GradedUnitZeroRing g u hu :=
  (gradedUnitNormalize g u hu).rangeRestrict

theorem gradedUnitZeroMap_surjective (g : DirectSum ℕ A →+* T) (u : Tˣ)
    (hu : ∀ x, Commute (g x) (u : T)) : Function.Surjective (gradedUnitZeroMap g u hu) :=
  RingHom.rangeRestrict_surjective _
end IntegrationInACVF.Section7
