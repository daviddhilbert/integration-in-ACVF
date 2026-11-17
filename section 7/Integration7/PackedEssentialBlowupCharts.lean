module

public import Integration7.EssentialBlowupChart
public import Integration7.GammaRVMapInverseGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual elementary charts can be packed into raw RV labels. The
inverse is the same actual essential chart inverse after unpacking. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)

def packedEssentialChartMap : Map W.essential.obj.domain
    (rvProductDomain U.essential.obj.domain (nonzeroBlowupConeSet S)) :=
  (rvPack U.essential.obj.domain (nonzeroBlowupConeSet S)).toImage.comp b.essentialChartMap

theorem packedEssentialChartMap_bijective : Function.Bijective b.packedEssentialChartMap :=
  (rvPackToImage_bijective _ _).comp b.essentialChartMap_bijective

theorem packedEssentialChartMap_inverse (w : rvProductDomain U.essential.obj.domain (nonzeroBlowupConeSet S)) :
    b.packedEssentialChartMap.inverse b.packedEssentialChartMap_bijective w =
      b.essentialChartInverseMap (rvUnpack U.essential.obj.domain (nonzeroBlowupConeSet S) w) := by
  apply b.packedEssentialChartMap_bijective.1
  change b.packedEssentialChartMap (b.packedEssentialChartMap.inverse b.packedEssentialChartMap_bijective w) = _
  rw [Map.apply_inverse]
  change w = (rvPack _ _).toImage (b.essentialChartMap
    (b.essentialChartInverseMap (rvUnpack _ _ w)))
  rw [essentialChartInverseMap,Map.apply_inverse,rvPack_unpack]

end IntegrationInACVF.Section7.ElementaryBlowup
