import IntegrationSection6.GammaNonzeroBasicFactors
import IntegrationSection6.GammaGradedResolution
import IntegrationSection6.FiniteGammaBasicRelation
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.GammaCompressionIsomorphisms
import IntegrationSection6.FiniteGammaPartitionCharts
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
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroOneClassAt : GammaNonzeroClassesAt (B := B) (S := S) 1 :=
  gammaNonzeroClassAt (gammaOneAt hBS.out) (gammaOneAt_fullWeight hBS.out)

def gammaNonzeroPositiveClassAt : GammaNonzeroClassesAt (B := B) (S := S) 1 :=
  gammaNonzeroClassAt (gammaHighRestrictionAt (gammaPositiveAt hBS.out)) (gammaHighRestriction_fullWeight _)

theorem gammaPositiveNonzeroAt_domain (t : Fin 1 → CanonicalRV.RVSort M) :
    t ∈ carrier (rvObjectDomain (gammaHighRestrictionAt (gammaPositiveAt hBS.out)).object.obj) ↔
      t ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (@positiveRV M N S) ∧
        (t 0).val ≠ @iRVZero M N := by
  change (t ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (@positiveRV M N S) ∧
    ¬ ∃ v : @positiveRV M N S, v.val = t ∧ ∃ i : Fin 1, (v.val i).val = @iRVZero M N) ↔ _
  constructor
  · rintro ⟨ht,hn⟩
    exact ⟨ht,fun hz => hn ⟨⟨t,ht⟩,rfl,⟨0,hz⟩⟩⟩
  · rintro ⟨ht,hn⟩
    refine ⟨ht,?_⟩
    rintro ⟨v,hv,i,hi⟩
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    exact hn ((congrArg (fun s => (s 0).val) hv).symm.trans hi)

theorem gammaGradedResolutionAt_one_factor :
    gammaGradedResolutionAt (gammaGradedClassAt (gammaOneAt hBS.out)) =
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 1 gammaNonzeroOneClassAt := by
  rw [gammaGradedClassAt,gammaGradedResolutionAt_of]
  exact gammaNonzeroResolutionAt_pure 1 gammaNonzeroOneClassAt

theorem gammaGradedResolutionAt_positive_factor :
    gammaGradedResolutionAt (gammaGradedClassAt (gammaPositiveAt hBS.out)) =
      1 + DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) 1 gammaNonzeroPositiveClassAt := by
  rw [gammaGradedClassAt,gammaGradedResolutionAt_of]
  rw [← gammaIsoClassAt_iso (gammaWeightSplitIsoAt (gammaPositiveAt hBS.out)),gammaIsoClassAt_coprod,map_add,
    ← gammaPaddingClassesAt_class,gammaNonzeroResolutionAt_padding,gammaIsoClassAt_iso (gammaPositiveZeroIsoUnitAt hBS.out)]
  have h0 : gammaNonzeroResolutionAt 0 (gammaIsoClassAt (gammaUnitAt hBS.out)) =
      (1 : GammaNonzeroGradedAt (B := B) (S := S)) :=
    gammaNonzeroResolutionAt_pure 0 (GradedMonoid.GOne.one : GammaNonzeroClassesAt (B := B) (S := S) 0)
  exact congrArg₂ (· + ·) h0 (gammaNonzeroResolutionAt_pure 1 gammaNonzeroPositiveClassAt)

end IntegrationInACVF.Section6.FiniteRV
