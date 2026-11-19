import Integration7.GammaNamedCoordinateKernel
import Integration7.RVVolumeLiftCommonContextKernel

/-! Gamma RV density graphs and their explicit lifts. The density graph of a
Gamma RV volume object is Gamma, the density-graph isomorphism has a Gamma
graph, and its lift is the explicit VF bijection appending the density as a
label (VF coordinates unchanged), with a Gamma graph. No general lifting of
RV isomorphisms is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open SpecialTransformations.Section9 (liftLabelMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_append_rv_volume_density (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    RVMapGamma (appendRVVolumeDensity U) G := by
  have hid : RVMapGamma (Map.id U.underlying.obj.domain).toUniv G :=
    (RVMapGamma.identity hc hU.domain_graph).congr (fun _ => rfl)
  exact (hid.append hU.density).congr (fun _ => rfl)

theorem gamma_rv_volume_density_projection (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    RVMapGamma (rvVolumeDensityProjection U) G := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((gammaLogicInput G).swap_graph (gamma_append_rv_volume_density hc hU))
  intro q p
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨(appendRVVolumeDensity U).toImage u,hq,?_⟩
    change ((appendRVVolumeDensity U).toImage.inverse _ ((appendRVVolumeDensity U).toImage u)).val = p.2
    rw [Map.inverse_apply]
    exact hu
  · rintro ⟨v,hv,hp⟩
    refine ⟨rvVolumeDensityProjection U v,hp,?_⟩
    exact (congrArg Subtype.val (Map.apply_inverse (appendRVVolumeDensity U).toImage
      (appendRVVolumeDensity_bijective U) v)).trans hv

theorem VolumeObjectGamma.densityGraph (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U G) :
    VolumeObjectGamma U.densityGraph G := by
  have hP := gamma_rv_volume_density_projection hc hU
  constructor
  · exact (hP.comp hU.coordinates).congr (fun _ => rfl)
  · exact (hP.comp hU.density).congr (fun _ => rfl)

theorem rv_volume_density_graph_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (hU : VolumeObjectGamma U G) :
    (rvVolumeDensityGraphIso hc C U).GammaDefinable G :=
  gamma_volume_iso_of_full_map _ (appendRVVolumeDensity U).toImage
    (gamma_essential_volume_domain _ hU.coordinates)
    ((gamma_append_rv_volume_density hc hU).congr (fun _ => rfl)) (fun _ => rfl)

theorem density_graph_lift_mem (U : PositiveRVVolumeObject (M := M) S k) (p : (rvVolumeLift U).domain) :
    (appendDensityMap (rvVolumeLift U).form p).val ∈ (rvLift U.densityGraph.underlying.obj).carrier := by
  obtain ⟨u,hu,hv⟩ := p.property
  have hl : liftLabelMap U.underlying.obj p = u := Subtype.ext hu.symm
  refine ⟨(appendRVVolumeDensity U).toImage u,?_,?_⟩
  · change Fin.append u.val (U.form.map u).val =
      Fin.append p.val.2 (U.form.map (liftLabelMap U.underlying.obj p)).val
    rw [hl,hu]
  · change U.underlying.obj.value ((appendRVVolumeDensity U).toImage.inverse _
      ((appendRVVolumeDensity U).toImage u)) = _
    rw [Map.inverse_apply]
    exact hv

/-- The explicit lift of the density-graph isomorphism: append the density as a label. -/
def densityGraphLiftMap (U : PositiveRVVolumeObject (M := M) S k) :
    Map (rvVolumeLift U).domain (rvVolumeLift U.densityGraph).domain :=
  (appendDensityMap (rvVolumeLift U).form).corestrict (density_graph_lift_mem U)

theorem densityGraphLiftMap_bijective (U : PositiveRVVolumeObject (M := M) S k) :
    Function.Bijective (densityGraphLiftMap U) := by
  constructor
  · intro p q he
    have h : (densityGraphLiftMap U p).val = (densityGraphLiftMap U q).val := congrArg Subtype.val he
    exact appendDensityMap_injective _ (Subtype.ext h)
  · intro q
    obtain ⟨v,hv,hval⟩ := q.property
    let u := rvVolumeDensityProjection U v
    have hvu : v = (appendRVVolumeDensity U).toImage u :=
      (Map.apply_inverse (appendRVVolumeDensity U).toImage (appendRVVolumeDensity_bijective U) v).symm
    have hmem : (q.val.1,u.val) ∈ (rvLift U.underlying.obj).carrier := by
      refine ⟨u,rfl,?_⟩
      exact hval
    refine ⟨⟨_,hmem⟩,Subtype.ext ?_⟩
    change (q.val.1,Fin.append u.val (U.form.map u).val) = q.val
    refine Prod.ext rfl ?_
    rw [← hv,hvu]
    rfl

def densityGraphLiftBijection (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection (rvVolumeLift U) (rvVolumeLift U.densityGraph) :=
  VFVolumeBijection.of_preserving_vf_and_density hc C (densityGraphLiftMap U)
    (densityGraphLiftMap_bijective U) (fun _ => rfl) (fun p => by
      change U.form.value (liftLabelMap U.underlying.obj p) =
        U.form.value ((appendRVVolumeDensity U).toImage.inverse _
          (⟨(densityGraphLiftMap U p).val.2,_⟩ : (appendRVVolumeDensity U).image))
      congr 1
      apply (appendRVVolumeDensity_bijective U).1
      rw [Map.apply_inverse]
      exact Subtype.ext rfl)

theorem density_graph_lift_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U G) :
    (VFVolumeIso.of_bijection (densityGraphLiftBijection hc C U)).GammaDefinable G := by
  have hL := gamma_rv_lift_carrier hc C hGC U hU
  have hD := gamma_rv_lift_carrier hc C hGC U.densityGraph (hU.densityGraph hc)
  have hDG : (volumeDensityGraph (rvVolumeLift U).form).carrier = (rvLift U.densityGraph.underlying.obj).carrier := by
    ext q
    constructor
    · rintro ⟨p,rfl⟩
      exact density_graph_lift_mem U p
    · intro hq
      obtain ⟨p,hp⟩ := (densityGraphLiftMap_bijective U).2 ⟨q,hq⟩
      exact ⟨p,congrArg Subtype.val hp⟩
  have hObj : VFVolumeObjectGamma (rvVolumeLift U) G := ⟨hL,hDG ▸ hD⟩
  refine ⟨hL,hD,?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hObj.projection_graph)
  intro p q
  constructor
  · rintro ⟨hq,hp⟩
    obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff _ q).mp hq
    refine ⟨⟨_,hq0⟩,hp.symm,?_⟩
    exact hqe.symm
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨density_graph_lift_mem U u |> fun h => ?_,?_⟩
    · rw [← hDG] at h
      exact h
    · change u.val = ((appendDensityMap (rvVolumeLift U).form u).val.1,
        (appendDensityMap (rvVolumeLift U).form u).val.2 ∘ Fin.castAdd 1)
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm

end IntegrationInACVF.Section7
