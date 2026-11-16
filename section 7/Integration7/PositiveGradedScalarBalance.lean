module

public import Integration7.SemimoduleScalarExtension
public import Integration7.GradedSemiringActions

@[expose] public section

/-! When a degree-one point maps to one, scalar compatibility for every
positive homogeneous coefficient implies compatibility for degree zero
and hence for every finite graded coefficient. No raw cancellation of
the point is required. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A : ℕ → Type} [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]
variable {S : Type} [Ring S] {P N : Type}
variable [AddCommMonoid P] [Module (DirectSum ℕ A) P]
variable [AddCommGroup N] [Module S N]

theorem graded_positive_scalar_balance (φ : DirectSum ℕ A →+* S) (I : P →+ N)
    (a : A 1) (ha : φ (DirectSum.of A 1 a)=1)
    (hPositive : ∀ i (u : A (i+1)) f,
      I (DirectSum.of A (i+1) u • f)=φ (DirectSum.of A (i+1) u) • I f)
    (r : DirectSum ℕ A) (f : P) : I (r • f)=φ r • I f := by
  have hPoint (g : P) : I (DirectSum.of A 1 a • g)=I g := by
    rw [hPositive 0 a g,ha,one_smul]
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul,map_zero,map_zero,zero_smul]
  | add r s hr hs => rw [add_smul,map_add,hr,hs,map_add,add_smul]
  | of i u =>
    cases i with
    | succ i => exact hPositive i u f
    | zero =>
      calc
        I (DirectSum.of A 0 u • f) = I (DirectSum.of A 1 a • (DirectSum.of A 0 u • f)) := (hPoint _).symm
        _ = I ((DirectSum.of A 1 a * DirectSum.of A 0 u) • f) := congrArg I (mul_smul _ _ f).symm
        _ = φ (DirectSum.of A 1 a * DirectSum.of A 0 u) • I f := by
          rw [DirectSum.of_mul_of]
          exact hPositive 0 (GradedMonoid.GMul.mul (i := 1) (j := 0) a u) f
        _ = φ (DirectSum.of A 0 u) • I f := by rw [map_mul,ha,one_mul]
end IntegrationInACVF.Section7
