import IntegrationSection6.GammaResolutionProducts
import IntegrationSection6.GammaWeightedPaddingProducts
import IntegrationSection6.GammaWeightDecomposition
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaAmbientIsos
import Section4.RVPaddingSplit
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

variable [Fact (B.real ⊆ S)]

def gammaGradedResolutionAt : GammaGradedClassesAt B S →+* GammaNonzeroGradedAt (B := B) (S := S) :=
  DirectSum.toSemiring (gammaNonzeroResolutionAt (B := B) (S := S))
    (by exact gammaNonzeroResolutionAt_pure 0 (GradedMonoid.GOne.one : GammaNonzeroClassesAt (B := B) (S := S) 0))
    (fun {i j} a b => gammaNonzeroResolutionAt_product (k := i) (l := j) a b)

theorem gammaGradedResolutionAt_of (k : ℕ) (a : GammaIsoClassesAt B S k) :
    gammaGradedResolutionAt (DirectSum.of (GammaIsoClassesAt B S) k a) = gammaNonzeroResolutionAt k a :=
  DirectSum.toSemiring_of _ _ _ k a

theorem gammaGradedResolutionAt_surjective : Function.Surjective (gammaGradedResolutionAt (B := B) (S := S)) := by
  intro a
  obtain ⟨k,x,rfl⟩ := gammaThroughToGradedAt_exhaustive a
  exact ⟨DirectSum.of (GammaIsoClassesAt B S) k (gammaFiniteWeightAssemblyAt k x),by
    rw [gammaGradedResolutionAt_of,gammaNonzeroResolutionAt_assembly]⟩

end IntegrationInACVF.Section6.FiniteRV
