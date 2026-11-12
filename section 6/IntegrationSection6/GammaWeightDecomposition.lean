import IntegrationSection6.GammaNonzeroClasses
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
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPadCompressIsoAt (U : GammaObjectAt B S (n+1))
    (hU : @rvLowWeightProperty M N S n U.object.obj) :
    GammaIsoAt (gammaPadAt (gammaCompressAt U hU)) U := by
  let A := gammaPadAt (gammaCompressAt U hU)
  let F := @SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S (rvObjectDomain U.object.obj)
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) A.object.obj u) =
      @rvWeight M N (n+1) (@RVObject.value M N S (n+1) U.object.obj (F u)) := by
    exact (@rvWeight_padRV M N hN n (@RVObject.value M N S n (gammaCompressAt U hU).object.obj u)).trans
      (@rvCompressObject_weight M N S n U.object.obj hU u)
  exact {
    iso := @isoOfDefinableBijection M N S (n+1) A.object U.object F Function.bijective_id hw
    graph := (gammaIsoRefl U.toGamma).graph }

theorem gammaHighRestriction_fullWeight (U : GammaObjectAt B S (n+1)) :
    GammaFullWeightAt (gammaHighRestrictionAt U) := by
  intro u
  let v : rvObjectDomain U.object.obj := ⟨u.val,u.property.1⟩
  have hle := @rvWeight_le_arity M N (n+1) (@RVObject.value M N S (n+1) U.object.obj v)
  have hn : ¬ @rvWeight M N (n+1) (@RVObject.value M N S (n+1) U.object.obj v) ≤ n := by
    intro h
    exact u.property.2 ((@mem_rvLowDomain M N S n U.object.obj v).mpr h)
  change @rvWeight M N (n+1) (@RVObject.value M N S (n+1) U.object.obj v) = n+1
  omega

theorem gammaFullWeightAt_iff_nonzero (U : GammaObjectAt B S n) :
    GammaFullWeightAt U ↔ ∀ u : rvObjectDomain U.object.obj, ∀ i,
      (@RVObject.value M N S n U.object.obj u i).val ≠ @iRVZero M N := by
  cases n with
  | zero =>
    constructor
    · intro _ _ i
      exact i.elim0
    · intro _ u
      exact Nat.eq_zero_of_le_zero (@rvWeight_le_arity M N 0 (@RVObject.value M N S 0 U.object.obj u))
  | succ n =>
    constructor
    · intro h u i hi
      have hl := (@rvWeight_le_pred_iff_zero M N n (@RVObject.value M N S (n+1) U.object.obj u)).mpr ⟨i,hi⟩
      have he := h u
      omega
    · intro h u
      have hn : ¬ @rvWeight M N (n+1) (@RVObject.value M N S (n+1) U.object.obj u) ≤ n := by
        intro hl
        obtain ⟨i,hi⟩ := (@rvWeight_le_pred_iff_zero M N n (@RVObject.value M N S (n+1) U.object.obj u)).mp hl
        exact h u i hi
      have hl := @rvWeight_le_arity M N (n+1) (@RVObject.value M N S (n+1) U.object.obj u)
      omega

def gammaWeightSplitIsoAt (U : GammaObjectAt B S (n+1)) :
    GammaIsoAt (gammaCoprodAt (gammaPadAt (gammaWeightProjectionAt U)) (gammaHighRestrictionAt U)) U :=
  (gammaCoprodIsoAt (gammaPadCompressIsoAt (gammaLowRestrictionAt U)
    (@rvLowRestriction_weight M N S n U.object.obj)) (GammaIsoAt.refl _)).trans
      (gammaPartitionIsoAt U (@rvLowDomain M N S n U.object.obj) (@rvLowDomain_subset M N S n U.object.obj)
        (gamma_low_volume_domain U.toGamma.toGammaRVObject))

end IntegrationInACVF.Section6.FiniteRV
