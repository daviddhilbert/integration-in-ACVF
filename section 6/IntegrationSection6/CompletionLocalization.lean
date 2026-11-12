import Section4.Imported.GrothendieckRing
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Dehomogenization of the group completion of a graded positive semiring.
The degree-one denominator may itself be a difference of positive classes. -/

noncomputable section

open Algebra

namespace IntegrationInACVF.Section6.CompletionLocalization

variable {A : ℕ → Type*} [∀ k, AddCommMonoid (A k)] [DirectSum.GCommSemiring A]

abbrev Ring (A : ℕ → Type*) [∀ k, AddCommMonoid (A k)] :=
  GrothendieckAddGroup (DirectSum ℕ A)

def homogeneous (k : ℕ) (a : A k) : Ring A :=
  GrothendieckAddGroup.ofRingHom (DirectSum.of A k a)

def pivot (a b : A 1) : Ring A := homogeneous 1 a - homogeneous 1 b
abbrev Target (a b : A 1) := Localization.Away (pivot a b)

def componentMap (a b : A 1) (k : ℕ) : A k →+ Target a b where
  toFun x := algebraMap (Ring A) (Target a b) (homogeneous k x) *
    IsLocalization.Away.invSelf (pivot a b) ^ k
  map_zero' := by simp [homogeneous]
  map_add' x y := by simp [homogeneous,add_mul]

private def positiveNormalization (a b : A 1) : DirectSum ℕ A →+* Target a b :=
  DirectSum.toSemiring (componentMap a b)
    (by
      change algebraMap (Ring A) (Target a b)
        (GrothendieckAddGroup.ofRingHom (1 : DirectSum ℕ A)) * _ ^ 0 = 1
      rw [map_one,map_one,pow_zero,mul_one])
    (by
      intro i k x y
      change algebraMap (Ring A) (Target a b)
        (homogeneous (i+k) (GradedMonoid.GMul.mul x y)) * _ ^ (i+k) = _
      have hm : homogeneous (i+k) (GradedMonoid.GMul.mul x y) =
          homogeneous i x * homogeneous k y := by
        rw [homogeneous,← DirectSum.of_mul_of,map_mul]
        rfl
      rw [hm,map_mul,pow_add]
      simp only [componentMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
      ring)

def normalize (a b : A 1) : Ring A →+* Target a b :=
  GrothendieckAddGroup.liftRingHom (positiveNormalization a b)

@[simp] theorem normalize_homogeneous (a b : A 1) (k : ℕ) (x : A k) :
    normalize a b (homogeneous k x) =
      algebraMap (Ring A) (Target a b) (homogeneous k x) *
        IsLocalization.Away.invSelf (pivot a b) ^ k := by
  change GrothendieckAddGroup.liftRingHom _
    (GrothendieckAddGroup.of (DirectSum.of A k x)) = _
  rw [GrothendieckAddGroup.liftRingHom_apply_of]
  exact DirectSum.toSemiring_of _ _ _ k x

@[simp] theorem normalize_pivot (a b : A 1) : normalize a b (pivot a b) = 1 := by
  change normalize a b (homogeneous 1 a - homogeneous 1 b) = 1
  rw [map_sub,normalize_homogeneous,normalize_homogeneous,pow_one,← sub_mul,← map_sub]
  change algebraMap (Ring A) (Target a b) (pivot a b) *
    IsLocalization.Away.invSelf (pivot a b) = 1
  exact IsLocalization.Away.mul_invSelf (S := Target a b) (pivot a b)

def relationIdeal (a b : A 1) : Ideal (Ring A) := Ideal.span {pivot a b - 1}

theorem relationIdeal_le_ker (a b : A 1) : relationIdeal a b ≤ RingHom.ker (normalize a b) := by
  rw [relationIdeal,Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  apply RingHom.mem_ker.mpr
  rw [map_sub,normalize_pivot,map_one,sub_self]

theorem quotient_pivot (a b : A 1) :
    Ideal.Quotient.mk (relationIdeal a b) (pivot a b) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (relationIdeal a b)),← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

private def evaluation (a b : A 1) : Target a b →+* (Ring A ⧸ relationIdeal a b) :=
  IsLocalization.Away.lift (pivot a b)
    (show IsUnit (Ideal.Quotient.mk (relationIdeal a b) (pivot a b)) by
      rw [quotient_pivot]; exact isUnit_one)

private theorem evaluation_algebraMap (a b : A 1) (x : Ring A) :
    evaluation a b (algebraMap (Ring A) (Target a b) x) =
      Ideal.Quotient.mk (relationIdeal a b) x := IsLocalization.Away.lift_eq _ _ _

private theorem evaluation_invSelf (a b : A 1) :
    evaluation a b (IsLocalization.Away.invSelf (pivot a b)) = 1 := by
  have h := congrArg (evaluation a b)
    (IsLocalization.Away.mul_invSelf (S := Target a b) (pivot a b))
  simpa only [map_mul,evaluation_algebraMap,quotient_pivot,one_mul,map_one] using h

private theorem evaluation_normalize (a b : A 1) :
    (evaluation a b).comp (normalize a b) = Ideal.Quotient.mk (relationIdeal a b) := by
  apply GrothendieckAddGroup.ringHom_ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    change evaluation a b (normalize a b (homogeneous k x)) = _
    rw [normalize_homogeneous,map_mul,map_pow,evaluation_algebraMap,
      evaluation_invSelf,one_pow,mul_one]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem normalize_kernel (a b : A 1) :
    RingHom.ker (normalize a b) = relationIdeal a b := by
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := DFunLike.congr_fun (evaluation_normalize a b) x
    rw [RingHom.comp_apply,RingHom.mem_ker.mp hx,map_zero] at he
    exact he.symm
  · exact relationIdeal_le_ker a b

/-- The localization map in6.22, on the actual kind of ring completion
used for RV scissors, after identification of the geometric ideal. -/
def quotientEmbedding (a b : A 1) : (Ring A ⧸ relationIdeal a b) →+* Target a b :=
  Ideal.Quotient.lift _ (normalize a b) (fun _ hx =>
    RingHom.mem_ker.mp (relationIdeal_le_ker a b hx))

theorem quotientEmbedding_injective (a b : A 1) : Function.Injective (quotientEmbedding a b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ (normalize_kernel a b).le

@[simp] theorem quotientEmbedding_mk_homogeneous (a b : A 1) (k : ℕ) (x : A k) :
    quotientEmbedding a b (Ideal.Quotient.mk (relationIdeal a b) (homogeneous k x)) =
      algebraMap (Ring A) (Target a b) (homogeneous k x) *
        IsLocalization.Away.invSelf (pivot a b) ^ k := normalize_homogeneous a b k x

end IntegrationInACVF.Section6.CompletionLocalization
