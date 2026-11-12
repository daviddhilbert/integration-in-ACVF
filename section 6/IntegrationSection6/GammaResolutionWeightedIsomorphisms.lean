import IntegrationSection6.GammaWeightedDegreeIsomorphisms
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

theorem gammaNonzeroResolutionAt_compression (U : GammaObjectAt B S (n+1))
    (hU : @rvLowWeightProperty M N S n U.object.obj) :
    gammaNonzeroResolutionAt (n+1) (gammaIsoClassAt U) =
      gammaNonzeroResolutionAt n (gammaIsoClassAt (gammaCompressAt U hU)) := by
  rw [← gammaIsoClassAt_iso (gammaPadCompressIsoAt U hU),← gammaPaddingClassesAt_class,gammaNonzeroResolutionAt_padding]

theorem gammaNonzeroResolutionAt_weightedIso {i j : ℕ} (U : GammaObjectAt B S i) (V : GammaObjectAt B S j)
    (e : GammaWeightedIsoAt U V) :
    gammaNonzeroResolutionAt i (gammaIsoClassAt U) = gammaNonzeroResolutionAt j (gammaIsoClassAt V) := by
  have aux : ∀ s i j, i+j = s → ∀ (U : GammaObjectAt B S i) (V : GammaObjectAt B S j),
      GammaWeightedIsoAt U V → gammaNonzeroResolutionAt i (gammaIsoClassAt U) = gammaNonzeroResolutionAt j (gammaIsoClassAt V) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro i j hs U V e
      rcases lt_trichotomy i j with hij | hij | hji
      · cases j with
        | zero => omega
        | succ j =>
          have hV := e.target_low (by omega)
          have he := ih (i+j) (by omega) i j rfl U (gammaCompressAt V hV) (e.compressTarget hV)
          exact he.trans (gammaNonzeroResolutionAt_compression V hV).symm
      · subst j
        exact congrArg (gammaNonzeroResolutionAt i) (gammaIsoClassAt_iso e.toIso)
      · cases i with
        | zero => omega
        | succ i =>
          have hU := e.source_low (by omega)
          have he := ih (i+j) (by omega) i j rfl (gammaCompressAt U hU) V (e.compressSource hU)
          exact (gammaNonzeroResolutionAt_compression U hU).trans he
  exact aux (i+j) i j rfl U V e

end IntegrationInACVF.Section6.FiniteRV
