import IntegrationSection6.GammaNonzeroClasses
import IntegrationSection6.GammaWeightStrata
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual original-Gamma RV[k] isomorphism
classes. This follows the pinned RVHomogeneousProducts/RVGradedSemiring
construction, using the finite Gamma structural maps proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem GammaFullWeightAt.product {l : ℕ} {U : GammaObjectAt B S k} {V : GammaObjectAt B S l}
    (hU : GammaFullWeightAt U) (hV : GammaFullWeightAt V) : GammaFullWeightAt (gammaProductAt U V) := by
  intro x
  obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) x
  exact (congrArg (@rvWeight M N (k+l)) (@rvProductObject_value_pair M N S k l U.object.obj V.object.obj u v)).trans
    ((@rvWeight_append M N k l (@RVObject.value M N S k U.object.obj u) (@RVObject.value M N S l V.object.obj v)).trans
      (congrArg₂ (· + ·) (hU u) (hV v)))

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroMulAt {i j : ℕ} (a : GammaNonzeroClassesAt (B := B) (S := S) i)
    (b : GammaNonzeroClassesAt (B := B) (S := S) j) : GammaNonzeroClassesAt (B := B) (S := S) (i+j) :=
  ⟨gammaClassMulAt a.val b.val,by
    obtain ⟨U,hu,hU⟩ := a.property
    obtain ⟨V,hv,hV⟩ := b.property
    rw [← hu,← hv,gammaClassMulAt_class]
    exact (gammaNonzeroClassAt_iff _).mpr (hU.product hV)⟩

instance gammaNonzeroGMulAt : GradedMonoid.GMul (GammaNonzeroClassesAt (B := B) (S := S)) :=
  ⟨gammaNonzeroMulAt⟩

instance gammaNonzeroGOneAt : GradedMonoid.GOne (GammaNonzeroClassesAt (B := B) (S := S)) :=
  ⟨gammaNonzeroClassAt (gammaUnitAt hBS.out) (fun u =>
    Nat.eq_zero_of_le_zero (@rvWeight_le_arity M N 0 (@RVObject.value M N S 0 (gammaUnitAt hBS.out).object.obj u)))⟩

def gammaNonzeroHomogeneousForget (a : GradedMonoid (GammaNonzeroClassesAt (B := B) (S := S))) :
    GradedMonoid (GammaIsoClassesAt B S) := ⟨a.1,a.2.val⟩

theorem gammaNonzeroHomogeneousForget_injective :
    Function.Injective (gammaNonzeroHomogeneousForget (B := B) (S := S)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hij := congrArg Sigma.fst h
  change i = j at hij
  subst j
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h).2)))

instance gammaNonzeroGCommMonoidAt : GradedMonoid.GCommMonoid (GammaNonzeroClassesAt (B := B) (S := S)) where
  one_mul a := by
    apply gammaNonzeroHomogeneousForget_injective
    exact one_mul (gammaNonzeroHomogeneousForget a)
  mul_one a := by
    apply gammaNonzeroHomogeneousForget_injective
    exact mul_one (gammaNonzeroHomogeneousForget a)
  mul_assoc a b c := by
    apply gammaNonzeroHomogeneousForget_injective
    exact mul_assoc (gammaNonzeroHomogeneousForget a) (gammaNonzeroHomogeneousForget b) (gammaNonzeroHomogeneousForget c)
  mul_comm a b := by
    apply gammaNonzeroHomogeneousForget_injective
    exact mul_comm (gammaNonzeroHomogeneousForget a) (gammaNonzeroHomogeneousForget b)

instance gammaNonzeroGNonUnitalNonAssocSemiringAt :
    DirectSum.GNonUnitalNonAssocSemiring (GammaNonzeroClassesAt (B := B) (S := S)) where
  mul_zero a := Subtype.ext (gammaClassMulAt_zero a.val)
  zero_mul b := Subtype.ext (gammaClassMulAt_zero_left b.val)
  mul_add a b c := Subtype.ext (gammaClassMulAt_add a.val b.val c.val)
  add_mul a b c := Subtype.ext (gammaClassMulAt_add_left a.val b.val c.val)

instance gammaNonzeroGSemiringAt : DirectSum.GSemiring (GammaNonzeroClassesAt (B := B) (S := S)) where
  natCast n := n • GradedMonoid.GOne.one
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul,one_nsmul]

instance gammaNonzeroGCommSemiringAt : DirectSum.GCommSemiring (GammaNonzeroClassesAt (B := B) (S := S)) where

abbrev GammaNonzeroGradedAt := DirectSum ℕ (GammaNonzeroClassesAt (B := B) (S := S))

def gammaNonzeroGradedClassAt (U : GammaObjectAt B S k) (hU : GammaFullWeightAt U) : GammaNonzeroGradedAt (B := B) (S := S) :=
  DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) k (gammaNonzeroClassAt U hU)

end IntegrationInACVF.Section6.FiniteRV
