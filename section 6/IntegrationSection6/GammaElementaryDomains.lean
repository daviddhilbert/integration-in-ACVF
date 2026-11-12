import IntegrationSection6.GammaRVRealSets
import IntegrationSection6.ElementaryCoordinates

/-! The elementary domain is Gamma-definable directly from its actual
product construction, over an arbitrary original real/Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_positiveRV : GammaSetDefinable B {p : Point (M := M) 0 1 |
    p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real (@positiveRV M N B.real)} :=
  gamma_rv_set_of_real (@positiveRV M N B.real)

theorem gamma_elementary_domain (U : GammaRVObject B n) (i : Fin n) :
    GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object+1) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes
        (rvObjectDomain (@elementary M N hN U.codes n U.object i))} :=
  gamma_rv_product_domain (rvObjectDomain U.object) (@positiveRV M N U.codes) U.domain_graph gamma_positiveRV

end IntegrationInACVF.Section6
