import Integration7.PackedEssentialBlowupCharts
import Integration7.GammaConeFibreMapGraphs
import Integration7.GammaHeadCorrectionGraphs
import Integration7.CorrectedBlowupMap

/-! Full original-Gamma essential charts and a Gamma head Jacobian
give the original-Gamma corrected elementary-blowup map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable)

namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem gamma_corrected_map
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {U V WU WV : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV)
    (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hf : f.GammaDefinable B)
    (hRaw : RVMapGamma (rawHeadCorrectionMap f J) B)
    (hb : RVMapGamma b.packedEssentialChartMap B)
    (hcchart : RVMapGamma c.packedEssentialChartMap B) :
    RVMapGamma (b.correctedMap c f J) B := by
  have hCone := gamma_packed_nonzero_cone_fibre_map hc (finiteIsoMap f.iso)
    (headCorrectionMap f J) (headCorrectionMap_absolute f J) hf
    (gamma_head_correction_map hc f J hRaw)
    (hb.range b.packedEssentialChartMap_bijective.2)
  have h := (hb.comp hCone).comp (hcchart.inverse c.packedEssentialChartMap_bijective)
  apply h.congr
  intro w
  simp only [Map.comp_apply]
  rw [c.packedEssentialChartMap_inverse]
  change (c.essentialChartInverseMap
    (rvUnpack _ _ (packedNonzeroConeFibreMap _ _ _ (b.packedEssentialChartMap w)))).val = _
  simp only [packedNonzeroConeFibreMap,Map.comp_apply,rvUnpack_pack,
    packedEssentialChartMap]
  rfl

end IntegrationInACVF.Section7.ElementaryBlowup
