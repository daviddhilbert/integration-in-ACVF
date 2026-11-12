import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Dehomogenization by a degree-one element, including injectivity after
quotienting by j-1. No regularity assumption on j is required. -/

noncomputable section

namespace IntegrationInACVF.Section6.GradedLocalization

variable {A : ℕ → Type*} [∀ k, AddCommGroup (A k)] [DirectSum.GCommRing A]

abbrev Ring (A : ℕ → Type*) [∀ k, AddCommGroup (A k)] := DirectSum ℕ A

def pivot (j : A 1) : Ring A := DirectSum.of A 1 j
abbrev Target (j : A 1) := Localization.Away (pivot j)

def componentMap (j : A 1) (k : ℕ) : A k →+ Target j where
  toFun a := algebraMap (Ring A) (Target j) (DirectSum.of A k a) *
    IsLocalization.Away.invSelf (pivot j) ^ k
  map_zero' := by simp
  map_add' a b := by simp [add_mul]

/-- Send a homogeneous degree-k element to its numerator divided by j^k. -/
def normalize (j : A 1) : Ring A →+* Target j :=
  DirectSum.toSemiring (componentMap j)
    (by
      change algebraMap (Ring A) (Target j)
        (DirectSum.of A 0 GradedMonoid.GOne.one) * _ ^ 0 = 1
      rw [pow_zero, mul_one]
      exact map_one _)
    (by
      intro i k a b
      change algebraMap (Ring A) (Target j)
        (DirectSum.of A (i+k) (GradedMonoid.GMul.mul a b)) *
          IsLocalization.Away.invSelf (pivot j) ^ (i+k) = _
      rw [← DirectSum.of_mul_of, map_mul, pow_add]
      simp only [componentMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      ring)

@[simp] theorem normalize_of (j : A 1) (k : ℕ) (a : A k) :
    normalize j (DirectSum.of A k a) = algebraMap (Ring A) (Target j)
      (DirectSum.of A k a) * IsLocalization.Away.invSelf (pivot j) ^ k :=
  DirectSum.toSemiring_of _ _ _ k a

@[simp] theorem normalize_pivot (j : A 1) : normalize j (pivot j) = 1 := by
  change normalize j (DirectSum.of A 1 j) = 1
  rw [normalize_of, pow_one]
  change algebraMap (Ring A) (Target j) (pivot j) *
    IsLocalization.Away.invSelf (pivot j) = 1
  exact IsLocalization.Away.mul_invSelf (S := Target j) (pivot j)

def relationIdeal (j : A 1) : Ideal (Ring A) := Ideal.span {pivot j - 1}

theorem relationIdeal_le_ker (j : A 1) : relationIdeal j ≤ RingHom.ker (normalize j) := by
  rw [relationIdeal, Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  apply RingHom.mem_ker.mpr
  rw [map_sub, normalize_pivot, map_one, sub_self]

theorem quotient_pivot (j : A 1) :
    Ideal.Quotient.mk (relationIdeal j) (pivot j) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (relationIdeal j)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

def evaluation (j : A 1) : Target j →+* (Ring A ⧸ relationIdeal j) :=
  IsLocalization.Away.lift (pivot j)
    (show IsUnit (Ideal.Quotient.mk (relationIdeal j) (pivot j)) by
      rw [quotient_pivot]; exact isUnit_one)

@[simp] theorem evaluation_algebraMap (j : A 1) (x : Ring A) :
    evaluation j (algebraMap (Ring A) (Target j) x) =
      Ideal.Quotient.mk (relationIdeal j) x :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem evaluation_invSelf (j : A 1) :
    evaluation j (IsLocalization.Away.invSelf (pivot j)) = 1 := by
  have h := congrArg (evaluation j) (IsLocalization.Away.mul_invSelf (S := Target j) (pivot j))
  simpa only [map_mul, evaluation_algebraMap, quotient_pivot, one_mul, map_one] using h

/-- Evaluation at j=1 is a retraction of dehomogenization modulo j-1. -/
theorem evaluation_normalize (j : A 1) :
    (evaluation j).comp (normalize j) = Ideal.Quotient.mk (relationIdeal j) := by
  apply DirectSum.ringHom_ext
  intro k a
  simp only [RingHom.comp_apply, normalize_of, map_mul, map_pow,
    evaluation_algebraMap, evaluation_invSelf, one_pow, mul_one]

/-- The exact kernel, including possible j-torsion in the graded ring. -/
theorem normalize_kernel (j : A 1) : RingHom.ker (normalize j) = relationIdeal j := by
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (fun f : Ring A →+* (Ring A ⧸ relationIdeal j) => f x)
      (evaluation_normalize j)
    rw [RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero] at h
    exact h.symm
  · exact relationIdeal_le_ker j

/-- The localization embedding used in Theorem 6.22 once the geometric
blowup ideal has been identified with this principal ideal. -/
def quotientEmbedding (j : A 1) : (Ring A ⧸ relationIdeal j) →+* Target j :=
  Ideal.Quotient.lift _ (normalize j) (fun _x hx =>
    RingHom.mem_ker.mp (relationIdeal_le_ker j hx))

theorem quotientEmbedding_injective (j : A 1) : Function.Injective (quotientEmbedding j) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ (normalize_kernel j).le

@[simp] theorem quotientEmbedding_mk_of (j : A 1) (k : ℕ) (a : A k) :
    quotientEmbedding j (Ideal.Quotient.mk (relationIdeal j) (DirectSum.of A k a)) =
      algebraMap (Ring A) (Target j) (DirectSum.of A k a) *
        IsLocalization.Away.invSelf (pivot j) ^ k := normalize_of j k a

end IntegrationInACVF.Section6.GradedLocalization
