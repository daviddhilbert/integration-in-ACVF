import IntegrationSection6.GammaNonzeroThroughTransitions
import IntegrationSection6.GammaPaddingClasses
import IntegrationSection6.GammaNonzeroGradedSemiring
import IntegrationSection6.GammaFiniteRestrictionIsomorphisms
import IntegrationSection6.FiniteGammaLocusBlowups
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

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroResolutionAt (k : ℕ) : GammaIsoClassesAt B S k →+ GammaNonzeroGradedAt (B := B) (S := S) :=
  (gammaThroughToGradedAt k).comp (gammaFiniteWeightAssemblyAt k).symm.toAddMonoidHom

theorem gammaFiniteWeightAssemblyAt_succ (n : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) (n+1)) :
    gammaFiniteWeightAssemblyAt (n+1) a = gammaPaddingClassesAt (gammaFiniteWeightAssemblyAt n a.1) + a.2.val := rfl

theorem gammaNonzeroResolutionAt_assembly (k : ℕ) (a : GammaNonzeroThroughAt (B := B) (S := S) k) :
    gammaNonzeroResolutionAt k (gammaFiniteWeightAssemblyAt k a) = gammaThroughToGradedAt k a := by
  change gammaThroughToGradedAt k ((gammaFiniteWeightAssemblyAt k).symm (gammaFiniteWeightAssemblyAt k a)) = _
  rw [AddEquiv.symm_apply_apply]

theorem gammaNonzeroResolutionAt_padding (k : ℕ) (a : GammaIsoClassesAt B S k) :
    gammaNonzeroResolutionAt (k+1) (gammaPaddingClassesAt a) = gammaNonzeroResolutionAt k a := by
  have he : (gammaFiniteWeightAssemblyAt (k+1)).symm (gammaPaddingClassesAt a) =
      gammaNonzeroThroughInclusionAt k ((gammaFiniteWeightAssemblyAt k).symm a) := by
    apply (gammaFiniteWeightAssemblyAt (k+1)).injective
    rw [AddEquiv.apply_symm_apply,gammaFiniteWeightAssemblyAt_compatible,AddEquiv.apply_symm_apply]
  change gammaThroughToGradedAt (k+1) ((gammaFiniteWeightAssemblyAt (k+1)).symm (gammaPaddingClassesAt a)) = _
  rw [he,gammaThroughToGradedAt_inclusion]
  rfl

theorem gammaNonzeroResolutionAt_pure (k : ℕ) (a : GammaNonzeroClassesAt (B := B) (S := S) k) :
    gammaNonzeroResolutionAt k a.val = DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) k a := by
  cases k with
  | zero =>
    change DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 0 ((gammaFiniteWeightAssemblyAt 0).symm a.val) = _
    congr 1
    apply Subtype.ext
    exact (gammaFiniteWeightAssemblyAt 0).apply_symm_apply a.val
  | succ n =>
    let x : GammaNonzeroThroughAt (B := B) (S := S) (n+1) := (0,a)
    have hx : gammaFiniteWeightAssemblyAt (n+1) x = a.val := by
      rw [gammaFiniteWeightAssemblyAt_succ]
      change gammaPaddingClassesAt (gammaFiniteWeightAssemblyAt n 0) + a.val = a.val
      rw [map_zero,map_zero,zero_add]
    rw [← hx,gammaNonzeroResolutionAt_assembly]
    change gammaThroughToGradedAt n 0 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) (n+1) a = _
    rw [map_zero,zero_add]

theorem gammaNonzeroResolutionAt_injective (k : ℕ) :
    Function.Injective (gammaNonzeroResolutionAt (B := B) (S := S) k) :=
  (gammaThroughToGradedAt_injective k).comp (gammaFiniteWeightAssemblyAt k).symm.injective

end IntegrationInACVF.Section6.FiniteRV
