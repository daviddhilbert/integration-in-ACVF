import IntegrationSection6.GammaRVRealMapGraphs
import IntegrationSection6.FiniteGammaRestrictions
import Section4.RVWeightRestriction
import IntegrationSection6.FiniteCoordinateDeletion
import IntegrationSection6.GammaFiniteSlices
import IntegrationSection6.FiniteGammaObjects

/-! Deleting an admissible volume coordinate keeps the actual object
in RV[k-1]. Finiteness uses the original-base algebraic label slices,
with no cardinal bound on the presentation codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_low_volume_domain (U : GammaRVObject B (n+1)) :
    GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
        (@CanonicalStructure.normalize M sM) _ U.codes (@rvLowDomain M (@CanonicalStructure.normalize M sM) U.codes n U.object)} := by
  have hZ := @gamma_rv_set_of_real M sM hM B (n+1) (@lowZeroLabels M N B.real n)
  have H := (gammaLogicInput B).image_graph ((gammaLogicInput B).restrict_graph hZ
    ((gammaLogicInput B).swap_graph U.volume_graph))
  convert H using 1
  ext p
  constructor
  · rintro ⟨u,hu,hz⟩
    exact ⟨(Fin.elim0,(rvObjectVolume U.object u).val),hz,u,hu,rfl⟩
  · rintro ⟨q,hq,u,hu,hv⟩
    refine ⟨u,hu,?_⟩
    change (rvObjectVolume U.object u).val ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes (@lowZeroLabels M N U.codes n)
    rw [hv]
    exact hq

def gammaLowRestrictionAt (U : GammaObjectAt B S (n+1)) : GammaObjectAt B S (n+1) :=
  gammaRestrictAt U (@rvLowDomain M (@CanonicalStructure.normalize M sM) S n U.object.obj)
    (@rvLowDomain_subset M (@CanonicalStructure.normalize M sM) S n U.object.obj)
    (gamma_low_volume_domain U.toGamma.toGammaRVObject)

def gammaHighRestrictionAt (U : GammaObjectAt B S (n+1)) : GammaObjectAt B S (n+1) :=
  gammaComplementAt U (@rvLowDomain M (@CanonicalStructure.normalize M sM) S n U.object.obj)
    (gamma_low_volume_domain U.toGamma.toGammaRVObject)

end IntegrationInACVF.Section6.FiniteRV
