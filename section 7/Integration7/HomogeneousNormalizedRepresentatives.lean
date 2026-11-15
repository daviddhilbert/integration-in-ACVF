import Mathlib.Algebra.DirectSum.Ring

/-! A degree-one point mapping to one homogenizes every finite graded
sum. The argument uses no commutativity of the graded semiring. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {A : ℕ → Type u} [∀ n, AddCommMonoid (A n)] [DirectSum.GSemiring A]
variable {T : Type v} [Semiring T]

theorem direct_sum_point_power_homogeneous (j : A 1) : ∀ m : ℕ,
    ∃ a : A m, (DirectSum.of A 1 j)^m = DirectSum.of A m a := by
  intro m
  induction m with
  | zero => exact ⟨GradedMonoid.GOne.one,rfl⟩
  | succ m ih =>
    obtain ⟨a,ha⟩ := ih
    exact ⟨GradedMonoid.GMul.mul a j,by rw [pow_succ,ha,DirectSum.of_mul_of]⟩

theorem normalized_homogeneous_shift_right (φ : DirectSum ℕ A →+* T) (j : A 1)
    (hj : φ (DirectSum.of A 1 j) = 1) {n : ℕ} (a : A n) (m : ℕ) :
    ∃ b : A (n+m), φ (DirectSum.of A n a) = φ (DirectSum.of A (n+m) b) := by
  obtain ⟨p,hp⟩ := direct_sum_point_power_homogeneous j m
  refine ⟨GradedMonoid.GMul.mul a p,?_⟩
  rw [←DirectSum.of_mul_of,←hp,map_mul,map_pow,hj,one_pow,mul_one]

theorem normalized_homogeneous_shift_left (φ : DirectSum ℕ A →+* T) (j : A 1)
    (hj : φ (DirectSum.of A 1 j) = 1) {m : ℕ} (a : A m) (n : ℕ) :
    ∃ b : A (n+m), φ (DirectSum.of A m a) = φ (DirectSum.of A (n+m) b) := by
  obtain ⟨p,hp⟩ := direct_sum_point_power_homogeneous j n
  refine ⟨GradedMonoid.GMul.mul p a,?_⟩
  rw [←DirectSum.of_mul_of,←hp,map_mul,map_pow,hj,one_pow,one_mul]

theorem normalized_finite_sum_homogeneous (φ : DirectSum ℕ A →+* T) (j : A 1)
    (hj : φ (DirectSum.of A 1 j) = 1) (x : DirectSum ℕ A) :
    ∃ n, ∃ a : A n, φ x = φ (DirectSum.of A n a) := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0,0,by rw [map_zero,map_zero,map_zero]⟩
  | of n a => exact ⟨n,a,rfl⟩
  | add x y hx hy =>
    obtain ⟨n,a,ha⟩ := hx
    obtain ⟨m,b,hb⟩ := hy
    obtain ⟨a',ha'⟩ := normalized_homogeneous_shift_right φ j hj a m
    obtain ⟨b',hb'⟩ := normalized_homogeneous_shift_left φ j hj b n
    exact ⟨n+m,a'+b',by rw [map_add,ha,hb,ha',hb',map_add,map_add]⟩

end IntegrationInACVF.Section7
