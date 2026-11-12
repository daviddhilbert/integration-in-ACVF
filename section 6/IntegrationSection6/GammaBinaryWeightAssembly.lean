import IntegrationSection6.GammaWeightBandIsomorphisms
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

def gammaWeightAssembleStepAt (n : ℕ) :
    (GammaIsoClassesAt B S n × GammaNonzeroClassesAt (B := B) (S := S) (n+1)) →+
      GammaIsoClassesAt B S (n+1) where
  toFun a := gammaPaddingClassesAt a.1 + a.2.val
  map_zero' := by simp
  map_add' a b := by
    change gammaPaddingClassesAt (a.1+b.1) + (a.2.val+b.2.val) = _
    rw [map_add]
    exact add_add_add_comm _ _ _ _

theorem gammaWeightAssembleStepAt_surjective (n : ℕ) :
    Function.Surjective (gammaWeightAssembleStepAt (B := B) (S := S) n) := by
  intro a
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  refine ⟨(gammaIsoClassAt (gammaWeightProjectionAt U),gammaNonzeroClassAt (gammaHighRestrictionAt U) (gammaHighRestriction_fullWeight U)),?_⟩
  change gammaPaddingClassesAt (gammaIsoClassAt (gammaWeightProjectionAt U)) + gammaIsoClassAt (gammaHighRestrictionAt U) = _
  rw [gammaPaddingClassesAt_class,← gammaIsoClassAt_coprod]
  exact gammaIsoClassAt_iso (gammaWeightSplitIsoAt U)

theorem gammaWeightAssembleStepAt_injective (n : ℕ) :
    Function.Injective (gammaWeightAssembleStepAt (B := B) (S := S) n) := by
  intro a b he
  obtain ⟨U,hu⟩ := gammaIsoClassAt_surjective a.1
  obtain ⟨C,hc⟩ := gammaIsoClassAt_surjective b.1
  obtain ⟨V,hv,hV⟩ := a.2.property
  obtain ⟨D,hd,hD⟩ := b.2.property
  have he' : gammaIsoClassAt (gammaCoprodAt (gammaPadAt U) V) = gammaIsoClassAt (gammaCoprodAt (gammaPadAt C) D) := by
    rw [gammaIsoClassAt_coprod,gammaIsoClassAt_coprod,← gammaPaddingClassesAt_class,← gammaPaddingClassesAt_class,hu,hc,hv,hd]
    exact he
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp he'
  have hU : @rvLowWeightProperty M N S n (gammaPadAt U).object.obj := fun u =>
    (@rvWeight_padRV M N (@CanonicalStructure.normalized_model M sM hM) n (@RVObject.value M N S n U.object.obj u)).le.trans
      (@rvWeight_le_arity M N n (@RVObject.value M N S n U.object.obj u))
  have hC : @rvLowWeightProperty M N S n (gammaPadAt C).object.obj := fun u =>
    (@rvWeight_padRV M N (@CanonicalStructure.normalized_model M sM hM) n (@RVObject.value M N S n C.object.obj u)).le.trans
      (@rvWeight_le_arity M N n (@RVObject.value M N S n C.object.obj u))
  obtain ⟨⟨el⟩,⟨er⟩⟩ := gammaIsoAt_weight_bands (gammaPadAt U) V (gammaPadAt C) D hU hV hC hD e
  apply Prod.ext
  · rw [← hu,← hc]
    apply gammaPaddingClassesAt_injective
    rw [gammaPaddingClassesAt_class,gammaPaddingClassesAt_class]
    exact gammaIsoClassAt_iso el
  · apply Subtype.ext
    rw [← hv,← hd]
    exact gammaIsoClassAt_iso er

def gammaWeightAssembleStepEquivAt (n : ℕ) :
    (GammaIsoClassesAt B S n × GammaNonzeroClassesAt (B := B) (S := S) (n+1)) ≃+
      GammaIsoClassesAt B S (n+1) :=
  AddEquiv.ofBijective (gammaWeightAssembleStepAt n)
    ⟨gammaWeightAssembleStepAt_injective n,gammaWeightAssembleStepAt_surjective n⟩

end IntegrationInACVF.Section6.FiniteRV
