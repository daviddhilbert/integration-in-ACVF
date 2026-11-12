import IntegrationSection6.CompletionLocalization
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The additive colimit in6.22. Additive maps out of a group completion
are specified on its positive monoid, so the component cocones below are
exactly cocones on the groups G(A[k]) with transition multiplication by j. -/
noncomputable section
open Algebra
namespace IntegrationInACVF.Section6.CompletionLocalization
variable {A : ℕ → Type*} [∀ k, AddCommMonoid (A k)] [DirectSum.GCommSemiring A]
variable (a b : A 1)
variable {X : Type*} [AddCommGroup X]

def Compatible (f : ∀ k, A k →+ X) : Prop :=
  ∀ k x, f (k+1) (GradedMonoid.GMul.mul x a) -
    f (k+1) (GradedMonoid.GMul.mul x b) = f k x

def gradedCoconeExtension (f : ∀ k, A k →+ X) : Ring A →+ X :=
  GrothendieckAddGroup.lift (DirectSum.toAddMonoid f)

theorem gradedCoconeExtension_homogeneous (f : ∀ k, A k →+ X) (k : ℕ) (x : A k) :
    gradedCoconeExtension f (homogeneous k x) = f k x := by
  change GrothendieckAddGroup.lift _ (GrothendieckAddGroup.of _) = _
  rw [GrothendieckAddGroup.lift_apply_of]
  exact DirectSum.toAddMonoid_of f k x

theorem homogeneous_mul (i k : ℕ) (x : A i) (y : A k) :
    homogeneous i x * homogeneous k y = homogeneous (i+k) (GradedMonoid.GMul.mul x y) := by
  rw [homogeneous,homogeneous,← map_mul,DirectSum.of_mul_of]
  rfl

theorem gradedCoconeExtension_pivot (f : ∀ k, A k →+ X) (hf : Compatible a b f)
    (r : Ring A) : gradedCoconeExtension f (r * pivot a b) = gradedCoconeExtension f r := by
  have hp (x : DirectSum ℕ A) :
      gradedCoconeExtension f (GrothendieckAddGroup.ofRingHom x * pivot a b) =
        gradedCoconeExtension f (GrothendieckAddGroup.ofRingHom x) := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of k x =>
      change gradedCoconeExtension f (homogeneous k x * (homogeneous 1 a - homogeneous 1 b)) = gradedCoconeExtension f (homogeneous k x)
      rw [mul_sub,map_sub,homogeneous_mul,homogeneous_mul,
        gradedCoconeExtension_homogeneous,gradedCoconeExtension_homogeneous,
        gradedCoconeExtension_homogeneous]
      exact hf k x
    | add x y hx hy => simpa only [map_add,add_mul] using congrArg₂ (· + ·) hx hy
  obtain ⟨x,y,rfl⟩ := GrothendieckAddGroup.exists_eq_sub_of r
  rw [sub_mul,map_sub,map_sub]
  exact congrArg₂ (· - ·) (hp x) (hp y)

def gradedColimitDesc (f : ∀ k, A k →+ X) (hf : Compatible a b f) :
    (Ring A ⧸ relationIdeal a b) →+ X :=
  QuotientAddGroup.lift (relationIdeal a b).toAddSubgroup (gradedCoconeExtension f) (by
    intro r hr
    obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton'.mp hr
    change gradedCoconeExtension f (s * (pivot a b - 1)) = 0
    rw [mul_sub,mul_one,map_sub,gradedCoconeExtension_pivot a b f hf,sub_self])

theorem gradedColimitDesc_homogeneous (f : ∀ k, A k →+ X) (hf : Compatible a b f)
    (k : ℕ) (x : A k) :
    gradedColimitDesc a b f hf (Ideal.Quotient.mk _ (homogeneous k x)) = f k x :=
  gradedCoconeExtension_homogeneous f k x

def gradedColimitComponent (k : ℕ) : A k →+ (Ring A ⧸ relationIdeal a b) :=
  (Ideal.Quotient.mk (relationIdeal a b)).toAddMonoidHom.comp
    (GrothendieckAddGroup.ofRingHom.toAddMonoidHom.comp (DirectSum.of A k))

theorem gradedColimitComponent_compatible : Compatible a b (gradedColimitComponent a b) := by
  intro k x
  change Ideal.Quotient.mk _ (homogeneous (k+1) (GradedMonoid.GMul.mul x a)) -
    Ideal.Quotient.mk _ (homogeneous (k+1) (GradedMonoid.GMul.mul x b)) =
      Ideal.Quotient.mk _ (homogeneous k x)
  rw [← map_sub,← homogeneous_mul,← homogeneous_mul,← mul_sub,map_mul]
  change _ * Ideal.Quotient.mk _ (pivot a b) = _
  rw [quotient_pivot,mul_one]

theorem gradedCoconeExtension_colimitComponent :
    gradedCoconeExtension (gradedColimitComponent a b) =
      (Ideal.Quotient.mk (relationIdeal a b)).toAddMonoidHom := by
  apply GrothendieckAddGroup.addHom_ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k x => exact gradedCoconeExtension_homogeneous (gradedColimitComponent a b) k x
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem gradedColimitDesc_unique (f : ∀ k, A k →+ X) (hf : Compatible a b f)
    (g : (Ring A ⧸ relationIdeal a b) →+ X)
    (hg : ∀ k x, g (Ideal.Quotient.mk _ (homogeneous k x)) = f k x) :
    g = gradedColimitDesc a b f hf := by
  have he : g.comp (Ideal.Quotient.mk (relationIdeal a b)).toAddMonoidHom =
      gradedCoconeExtension f := by
    apply GrothendieckAddGroup.addHom_ext
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of k x => exact (hg k x).trans (gradedCoconeExtension_homogeneous f k x).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  ext q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact DFunLike.congr_fun he r

/-- The universal property of the filtered additive colimit under ×j. -/
theorem gradedColimit_universal (f : ∀ k, A k →+ X) (hf : Compatible a b f) :
    ∃! g : (Ring A ⧸ relationIdeal a b) →+ X,
      ∀ k x, g (Ideal.Quotient.mk _ (homogeneous k x)) = f k x :=
  ⟨gradedColimitDesc a b f hf,gradedColimitDesc_homogeneous a b f hf,
    fun g hg => gradedColimitDesc_unique a b f hf g hg⟩

end IntegrationInACVF.Section6.CompletionLocalization
