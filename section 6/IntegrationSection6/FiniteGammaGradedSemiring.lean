import IntegrationSection6.FiniteGammaClassProducts
import Mathlib.Algebra.DirectSum.Ring

/-! The graded semiring of actual original-Gamma RV[k] isomorphism
classes. This follows the pinned RVHomogeneousProducts/RVGradedSemiring
construction, using the finite Gamma structural maps proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}
local notation "N" => (@CanonicalStructure.normalize M sM)

instance gammaClassesGMulAt : GradedMonoid.GMul (GammaIsoClassesAt B S) := ⟨gammaClassMulAt⟩

variable [hBS : Fact (B.real ⊆ S)]

instance gammaClassesGOneAt : GradedMonoid.GOne (GammaIsoClassesAt B S) :=
  ⟨gammaIsoClassAt (gammaUnitAt hBS.out)⟩

theorem gammaHomogeneous_mul_comm (a b : GradedMonoid (GammaIsoClassesAt B S)) : a*b = b*a := by
  obtain ⟨k,a⟩ := a
  obtain ⟨l,b⟩ := b
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  change (⟨k+l,gammaClassMulAt (gammaIsoClassAt U) (gammaIsoClassAt V)⟩ : GradedMonoid (GammaIsoClassesAt B S)) =
    ⟨l+k,gammaClassMulAt (gammaIsoClassAt V) (gammaIsoClassAt U)⟩
  rw [gammaClassMulAt_class,gammaClassMulAt_class]
  exact Sigma.ext (Nat.add_comm k l)
    (gammaClass_heq_of_reindexedIso (Nat.add_comm k l) _ _ finAddFlip (gammaProductCommReindexedIsoAt U V))

theorem gammaHomogeneous_mul_one (a : GradedMonoid (GammaIsoClassesAt B S)) : a*1 = a := by
  obtain ⟨k,a⟩ := a
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  change (⟨k+0,gammaClassMulAt (gammaIsoClassAt U) (gammaIsoClassAt (gammaUnitAt hBS.out))⟩ : GradedMonoid (GammaIsoClassesAt B S)) =
    ⟨k,gammaIsoClassAt U⟩
  rw [gammaClassMulAt_class]
  exact Sigma.ext (Nat.add_zero k) (heq_of_eq (gammaIsoClassAt_iso (gammaProductRightUnitIsoAt U)))

theorem gammaHomogeneous_mul_assoc (a b c : GradedMonoid (GammaIsoClassesAt B S)) : a*b*c = a*(b*c) := by
  obtain ⟨k,a⟩ := a
  obtain ⟨l,b⟩ := b
  obtain ⟨j,c⟩ := c
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  obtain ⟨W,rfl⟩ := gammaIsoClassAt_surjective c
  change (⟨(k+l)+j,gammaClassMulAt (gammaClassMulAt (gammaIsoClassAt U) (gammaIsoClassAt V)) (gammaIsoClassAt W)⟩ : GradedMonoid (GammaIsoClassesAt B S)) =
    ⟨k+(l+j),gammaClassMulAt (gammaIsoClassAt U) (gammaClassMulAt (gammaIsoClassAt V) (gammaIsoClassAt W))⟩
  rw [gammaClassMulAt_class,gammaClassMulAt_class,gammaClassMulAt_class,gammaClassMulAt_class]
  exact Sigma.ext (Nat.add_assoc k l j)
    (gammaClass_heq_of_reindexedIso (Nat.add_assoc k l j) _ _ (finCongr (Nat.add_assoc k l j))
      (gammaProductAssocReindexedIsoAt U V W))

instance gammaClassesGCommMonoidAt : GradedMonoid.GCommMonoid (GammaIsoClassesAt B S) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul a := by rw [gammaHomogeneous_mul_comm,gammaHomogeneous_mul_one]
  mul_one := gammaHomogeneous_mul_one
  mul_assoc := gammaHomogeneous_mul_assoc
  mul_comm := gammaHomogeneous_mul_comm

theorem gammaClassMulAt_zero {k l : ℕ} (a : GammaIsoClassesAt B S k) :
    gammaClassMulAt a (0 : GammaIsoClassesAt B S l) = 0 := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  rw [← gammaIsoClassAt_empty (n := l) hBS.out,gammaClassMulAt_class]
  apply gammaIsoClassAt_eq_zero
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u,v,_⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj)
      (rvObjectDomain (gammaEmptyAt (n := l) hBS.out).object.obj) ⟨x,hx⟩
    exact v.property.elim
  · exact Set.empty_subset _

theorem gammaClassMulAt_zero_left {k l : ℕ} (b : GammaIsoClassesAt B S l) :
    gammaClassMulAt (0 : GammaIsoClassesAt B S k) b = 0 := by
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [← gammaIsoClassAt_empty (n := k) hBS.out,gammaClassMulAt_class]
  apply gammaIsoClassAt_eq_zero
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u,v,_⟩ := @exists_rvPackPair M N S _ _
      (rvObjectDomain (gammaEmptyAt (n := k) hBS.out).object.obj) (rvObjectDomain V.object.obj) ⟨x,hx⟩
    exact u.property.elim
  · exact Set.empty_subset _

instance gammaClassesGNonUnitalNonAssocSemiringAt : DirectSum.GNonUnitalNonAssocSemiring (GammaIsoClassesAt B S) where
  mul_zero := gammaClassMulAt_zero
  zero_mul := gammaClassMulAt_zero_left
  mul_add := gammaClassMulAt_add
  add_mul := gammaClassMulAt_add_left

instance gammaClassesGSemiringAt : DirectSum.GSemiring (GammaIsoClassesAt B S) where
  natCast n := n • gammaIsoClassAt (gammaUnitAt hBS.out)
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp only [succ_nsmul,one_nsmul]; rfl

instance gammaClassesGCommSemiringAt : DirectSum.GCommSemiring (GammaIsoClassesAt B S) where

abbrev GammaGradedClassesAt (B : Base (M := M)) (S : Set M) [Fact (B.real ⊆ S)] :=
  DirectSum ℕ (GammaIsoClassesAt B S)

def gammaGradedClassAt {k : ℕ} (U : GammaObjectAt B S k) : GammaGradedClassesAt B S :=
  DirectSum.of (GammaIsoClassesAt B S) k (gammaIsoClassAt U)

theorem gammaGradedClassAt_product {k l : ℕ} (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    gammaGradedClassAt (gammaProductAt U V) = gammaGradedClassAt U * gammaGradedClassAt V := by
  rw [gammaGradedClassAt,gammaGradedClassAt,gammaGradedClassAt,DirectSum.of_mul_of]
  exact congrArg (DirectSum.of (GammaIsoClassesAt B S) (k+l)) (gammaClassMulAt_class U V).symm

theorem gammaGradedClassAt_coprod {k : ℕ} (U V : GammaObjectAt B S k) :
    gammaGradedClassAt (gammaCoprodAt U V) = gammaGradedClassAt U + gammaGradedClassAt V := by
  change DirectSum.of (GammaIsoClassesAt B S) k (gammaIsoClassAt (gammaCoprodAt U V)) = _
  rw [gammaIsoClassAt_coprod,map_add]
  rfl

end IntegrationInACVF.Section6.FiniteRV
