module

public import Integration7.NativeUnaryRectangleVolumeObjects
public import Integration7.GammaEssentialVolumeGraphs
public import Integration7.GammaVolumeDensityRescaling
public import IntegrationSection6.GammaRawStandardContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The exact rectangle product volume isomorphism retains its full
original-Gamma graph, at any common nonzero constant density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (SpecialBijection IsRVPullback pullbackObject headImage
  GammaChainDefinable GammaSetDefinable Point)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {m r b : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
variable {E : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable (T : SpecialBijection A D) (hT : GammaChainDefinable P T.chain)
variable (hD : IsRVPullback (SpecialTransformations.Section5.carrier D))
variable {W : SpecialBijection B E} (hW : GammaChainDefinable P W.chain)
variable (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P)
variable (hDF : (canonicalRVObject hc (pullbackObject D)).volume.FiniteFibres)
variable (hEF : (canonicalRVObject hc (pullbackObject E)).volume.FiniteFibres)
include hT hW

theorem native_rectangle_raw_unit_volume_coordinates_gamma :
    RVMapGamma (nativeRectangleRawUnitVolume hc T hD L hDF hEF).underlying.obj.volume P := by
  let K := nativeUnaryRectangleContraction T hD L
  have hK := gamma_native_unary_rectangle_contraction T hT hD hW L
  have hSource := gamma_raw_contraction_domain K (gamma_program_final_set K.program hK)
  exact gamma_real_rv_map_graph hc P _ (rvCoordinateSelectMap P.real K.volumeIndex) hSource (fun _ => rfl)

theorem native_rectangle_raw_volume_iso_gamma :
    (nativeRectangleRawVolumeIso hc C T hD L hDF hEF).GammaDefinable P := by
  exact gamma_volume_iso_of_preserving_coordinates_full hc C
    (nativeRectangleRawFiniteRVIso hc T hD L hDF hEF)
    (native_rectangle_raw_finite_rv_iso_volume hc T hD L hDF hEF) (fun _ => rfl)
    (gamma_essential_volume_domain _ (native_rectangle_raw_unit_volume_coordinates_gamma hc C T hT hD hW L hDF hEF))
    (native_rectangle_raw_product_map_gamma hc T hD L)

theorem native_rectangle_raw_constant_density_volume_comparison
    (η : CanonicalRV.RVSort M) (hη : η.val ∈ C.base) (hη0 : η ≠ 0) :
    ∃ e : RVVolumeIso ((nativeRectangleRawUnitVolume hc T hD L hDF hEF).rescale η hη hη0)
      ((unaryProductUnitVolumeObject hc hDF hEF).rescale η hη hη0), e.GammaDefinable P :=
  ⟨(nativeRectangleRawVolumeIso hc C T hD L hDF hEF).rescale η hη hη0,
    (native_rectangle_raw_volume_iso_gamma hc C T hT hD hW L hDF hEF).rescale η hη hη0⟩

end IntegrationInACVF.Section7
