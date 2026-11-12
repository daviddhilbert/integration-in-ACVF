import IntegrationSection6.IntegrationContexts
import IntegrationSection6.GlobalLiftClassEquality
import IntegrationSection6.GammaResolutionProducts

/-! Addition and multiplication formulas for actual RV representatives
in a context's coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {k l : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

abbrev IntegrationContext.rvClass (P : IntegrationContext B κ hs) (U : GammaObjectAt B Set.univ k) : P.RV :=
  rvGlobalIntegralClass P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.section5_two_order P.generated U.toGamma

theorem IntegrationContext.rvClass_coprod (P : IntegrationContext B κ hs) (U V : GammaObjectAt B Set.univ k) :
    P.rvClass (gammaCoprodAt U V) = P.rvClass U + P.rvClass V := by
  simp only [IntegrationContext.rvClass,rvGlobalIntegralClass_at,gammaIsoClassAt_coprod,map_add]

theorem IntegrationContext.rvClass_product (P : IntegrationContext B κ hs)
    (U : GammaObjectAt B Set.univ k) (V : GammaObjectAt B Set.univ l) :
    P.rvClass (gammaProductAt U V) = P.rvClass U * P.rvClass V := by
  simp only [IntegrationContext.rvClass,rvGlobalIntegralClass_at,← gammaClassMulAt_class,
    gammaNonzeroResolutionAt_product,map_mul]

theorem IntegrationContext.rvClass_padding (P : IntegrationContext B κ hs) (U : GammaObjectAt B Set.univ k) :
    P.rvClass (gammaPadAt U) = P.rvClass U := by
  simp only [IntegrationContext.rvClass,rvGlobalIntegralClass_at,← gammaPaddingClassesAt_class,
    gammaNonzeroResolutionAt_padding]

theorem IntegrationContext.rvClass_empty (P : IntegrationContext B κ hs) :
    P.rvClass (gammaEmptyAt (n := k) (Set.subset_univ _)) = 0 := by
  simp only [IntegrationContext.rvClass,rvGlobalIntegralClass_at,gammaIsoClassAt_empty,map_zero]

end IntegrationInACVF.Section6.FiniteRV
