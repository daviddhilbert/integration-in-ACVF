module

public import Integration7.GammaRVScalarMapGraphs
public import Integration7.GammaEssentialCoordinateGraphs
public import Integration7.DefinableHeadCorrection

@[expose] public section

/-! The actual Jacobian correction, including its unit fallback, has
its full graph over the original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_raw_head_correction_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      U.underlying.obj.volume.graph p.2 q.2))
    (hV : GammaGraphDefinable B (fun (p : Point (M := M) 0 V.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
      V.underlying.obj.volume.graph p.2 q.2))
    (hω : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 1) =>
      U.form.map.graph p.2 q.2))
    (hπ : GammaGraphDefinable B (fun (p : Point (M := M) 0 V.underlying.obj.arity) (q : Point (M := M) 0 1) =>
      V.form.map.graph p.2 q.2))
    (hf : f.GammaDefinable B) (hJ : RVMapGamma J B) : RVMapGamma (rawHeadCorrectionMap f J) B := by
  have hF : RVMapGamma (finiteIsoMap f.iso) B := hf
  have hUcoords : RVMapGamma U.essential.obj.volume B := gamma_essential_coordinate_graph U hU
  have hVcoords : RVMapGamma V.essential.obj.volume B := gamma_essential_coordinate_graph V hV
  have hUform : RVMapGamma U.essentialForm.map B := gamma_essential_density_graph U hU hω
  have hVform : RVMapGamma V.essentialForm.map B := gamma_essential_density_graph V hV hπ
  have hR := hUcoords.select hc (fun _ : Fin 1 => Fin.last k)
  have hS := (hF.comp hVcoords).select hc (fun _ : Fin 1 => Fin.last k)
  have hRatio := hUform.scalarMul hc ((hF.comp hVform).inverseScalar hc)
  have hDen := hJ.scalarMul hc (hS.scalarMul hc (hR.inverseScalar hc))
  exact hRatio.scalarMul hc (hDen.inverseScalar hc)

theorem gamma_head_correction_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) S))
    (hRaw : RVMapGamma (rawHeadCorrectionMap f J) B) : RVMapGamma (headCorrectionMap f J) B :=
  hRaw.unitNormalize hc

end IntegrationInACVF.Section7
