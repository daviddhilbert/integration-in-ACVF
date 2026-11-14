import Integration7.EssentialBlowupChart
import Integration7.DefinableHeadCorrection
import Integration7.NondegenerateFiniteIso
import Integration7.GammaVolumeCriterion
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open scoped BigOperators
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem blowupCoordinates_absolute_product (t : Fin (k+1) → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) :
    (∏ i, RVOperations.absoluteHom (blowupCoordinates t s i)) =
      RVOperations.absoluteHom s * ∏ i, RVOperations.absoluteHom (t i) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc (fun i => RVOperations.absoluteHom (t i))]
  simp only [blowupCoordinates_head, blowupCoordinates_last, map_mul]
  ac_rfl

variable {U V : PositiveRVVolumeObject (M := M) S k}

def correctedConeFibreMap (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Map (U.essential.obj.domain.prod (nonzeroBlowupConeSet S))
      (V.essential.obj.domain.prod (nonzeroBlowupConeSet S)) :=
  nonzeroConeFibreMap (finiteIsoMap f.iso) (headCorrectionMap f J) (headCorrectionMap_absolute f J)

theorem correctedConeFibreMap_bijective (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Function.Bijective (correctedConeFibreMap f J) :=
  nonzeroConeFibreMap_bijective (finiteIsoMap f.iso)
    ⟨finiteIsoMap_injective f.iso, fun v => ⟨finiteIsoMap f.iso.symm v, finiteIsoMap_apply_symm f.iso v⟩⟩
    (headCorrectionMap f J) (headCorrectionMap_absolute f J)

namespace ElementaryBlowup
variable {WU WV : PositiveRVVolumeObject (M := M) S k}
variable (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV)

def correctedMap (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Map WU.essential.obj.domain WV.essential.obj.domain :=
  c.essentialChartInverseMap.comp ((correctedConeFibreMap f J).comp b.essentialChartMap)

theorem correctedMap_bijective (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    Function.Bijective (b.correctedMap c f J) :=
  (Equiv.ofBijective c.essentialChartMap c.essentialChartMap_bijective).symm.bijective.comp
    ((correctedConeFibreMap_bijective f J).comp b.essentialChartMap_bijective)

theorem correctedMap_chart (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) :
    c.essentialChartMap (b.correctedMap c f J w) = correctedConeFibreMap f J (b.essentialChartMap w) :=
  Map.apply_inverse c.essentialChartMap c.essentialChartMap_bijective _

theorem correctedMap_density (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) :
    WV.essentialForm.value (b.correctedMap c f J w) =
      V.essentialForm.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) := by
  rw [c.essentialChart_density]
  apply congrArg V.essentialForm.value
  exact congrArg (fun p : V.essential.obj.domain.prod (nonzeroBlowupConeSet S) =>
    (⟨p.val.1, p.property.1⟩ : V.essential.obj.domain)) (b.correctedMap_chart c f J w)

theorem correctedMap_coordinates (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) :
    WV.essential.obj.value (b.correctedMap c f J w) =
      blowupCoordinates (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))))
        ((headCorrectionMap f J (Map.prodFst _ _ (b.essentialChartMap w))).val 0 *
          (b.essentialChartMap w).val.2 0) := by
  rw [c.essentialChart_coordinates, b.correctedMap_chart]
  rfl

def correctedIso (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S)) :
    WU.essential ≅ WV.essential :=
  finiteIsoOfNondegenerateBijection (b.correctedMap c f J) (b.correctedMap_bijective c f J)
    WU.essential_nonzero WV.essential_nonzero

theorem correctedMap_weight_ratio (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) :
    (∏ i, RVOperations.absoluteHom (WV.essential.obj.value (b.correctedMap c f J w) i)) /
        (∏ i, RVOperations.absoluteHom (WU.essential.obj.value w i)) =
      (∏ i, RVOperations.absoluteHom
        (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) i)) /
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)) i) := by
  have ht : RVOperations.absoluteHom ((b.essentialChartMap w).val.2 0) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr
      (((mem_nonzeroBlowupConeSet S _).mp (b.essentialChartMap w).property.2).2)
  rw [b.correctedMap_coordinates, b.essentialChart_coordinates,
    blowupCoordinates_absolute_product, blowupCoordinates_absolute_product, map_mul,
    headCorrectionMap_absolute, one_mul, mul_div_mul_left _ _ ht]

theorem correctedIso_gamma (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (w : WU.essential.obj.domain) :
    Values.vrv (WU.essentialForm.value w) =
      Values.vrv (WV.essentialForm.value (finiteIsoMap (b.correctedIso c f J) w)) *
        (rvGammaJacobian (WU.essential.obj.value w)
          (WV.essential.obj.value (finiteIsoMap (b.correctedIso c f J) w))
          (WU.essential_nonzero w) (WV.essential_nonzero (finiteIsoMap (b.correctedIso c f J) w))).val := by
  apply gammaVolumeEquation_of_absoluteRatio
  change RVOperations.absoluteHom (WU.essentialForm.value w / WV.essentialForm.value (b.correctedMap c f J w)) =
    (∏ i, RVOperations.absoluteHom (WV.essential.obj.value (b.correctedMap c f J w) i)) /
      ∏ i, RVOperations.absoluteHom (WU.essential.obj.value w i)
  rw [b.essentialChart_density, b.correctedMap_density]
  rw [b.correctedMap_weight_ratio c f J w]
  exact f.absolute_volumeRatio (Map.prodFst _ _ (b.essentialChartMap w))
end ElementaryBlowup
end IntegrationInACVF.Section7
