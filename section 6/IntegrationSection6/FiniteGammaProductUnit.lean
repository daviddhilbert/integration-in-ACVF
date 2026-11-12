import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.GammaRVGlobalRestriction
import IntegrationSection6.FiniteGammaFormulaIsos
import IntegrationSection6.ProductStructuralCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaUnitAt (hBS : B.real ⊆ S) : GammaObjectAt B S 0 where
  object := @rvFiniteUnitObject M N S
  real_contains := hBS
  domain_graph := gamma_rv_set_of_real
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real)
  volume_graph := gamma_rv_graph_of_global_formula
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ S
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) S))
    (@SpecialTransformations.DefinableGeometry.Map.id LRV M N _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real))
    (gamma_rv_set_of_real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N 0) B.real))
    (fun _ => rfl)

def gammaProductRightUnitIsoAt (U : GammaObjectAt B S k) :
    GammaIsoAt (gammaProductAt U (gammaUnitAt U.real_contains)) U :=
  GammaIsoAt.ofAmbientFormula (@rvProductRightUnitIso M N S k U.object.obj)
    (@selectRVTuple M N B.real ((rvObjectArity U.object.obj)+0) (rvObjectArity U.object.obj) (Fin.castAdd 0)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N ((rvObjectArity U.object.obj)+0)) B.real))
    (fun x => @rvProductRightUnitMap_labels M N S k U.object.obj x)

end IntegrationInACVF.Section6.FiniteRV
