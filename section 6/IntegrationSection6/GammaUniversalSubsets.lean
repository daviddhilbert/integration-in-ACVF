import IntegrationSection6.GammaRVSetRealization
import IntegrationSection6.FiniteGammaUniversalCharts

/-! Original-Gamma RV loci have native definable-set presentations at a
common internal code universe. That universe is never added to the original
base and carries no saturation smallness hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem exists_gammaUniversalDefSet (D : Set (Fin a → RV (M := M)))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D}) :
    ∃ A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N a) (Set.univ : Set M),
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A = D := by
  obtain ⟨d,t,hd⟩ := gamma_rv_set_real_specialize D hD
  have h := @SpecialTransformations.DefinableGeometry.Space.Definable.mono LRV M N
    (@rawRVSpace M N a) (B.real ∪ Set.range (rawTuple t)) Set.univ D hd (Set.subset_univ _)
  exact ⟨@SpecialTransformations.DefinableGeometry.DefSet.mk LRV M N (@rawRVSpace M N a) Set.univ D h,rfl⟩

end IntegrationInACVF.Section6
