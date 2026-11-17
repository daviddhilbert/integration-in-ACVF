module

public import Integration7.NativeUnaryRectangleRawIsomorphisms
public import Integration7.SmallDimensionContractionNormalization
public import Integration7.VolumeRelabeling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The constructed rectangle output has actual finite volume whenever
the two unary preparations do. Its product comparison is a full volume
isomorphism, with no lower-dimensionality assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (SpecialBijection IsRVPullback pullbackObject headImage)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m r b : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S 1 m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) S 1 0}
variable {E : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (T : SpecialBijection A D) (hD : IsRVPullback (SpecialTransformations.Section5.carrier D))
variable {W : SpecialBijection B E}
variable (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P)
variable (hDF : (canonicalRVObject hc (pullbackObject D)).volume.FiniteFibres)
variable (hEF : (canonicalRVObject hc (pullbackObject E)).volume.FiniteFibres)

include hDF hEF in
theorem native_rectangle_raw_finite_volume :
    (canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject).volume.FiniteFibres :=
  (finite_volume_iso (nativeRectangleRawRVIso hc T hD L)).mpr (rvProductObject_finite_volume _ _ hDF hEF)

def unaryProductUnitVolumeObject : PositiveRVVolumeObject (M := M) S 1 :=
  ⟨rvFiniteProductObject ⟨canonicalRVObject hc (pullbackObject D),hDF⟩
    ⟨canonicalRVObject hc (pullbackObject E),hEF⟩,VolumeForm.one _⟩

def nativeRectangleRawUnitVolume : PositiveRVVolumeObject (M := M) S 1 :=
  rawUnitVolumeContraction hc (nativeUnaryRectangleContraction T hD L)
    (native_rectangle_raw_finite_volume hc T hD L hDF hEF)

def nativeRectangleRawFiniteRVIso :
    (nativeRectangleRawUnitVolume hc T hD L hDF hEF).underlying ≅
      (unaryProductUnitVolumeObject hc hDF hEF).underlying :=
  rvFiniteIsoOfAmbient (nativeRectangleRawRVIso hc T hD L)

theorem native_rectangle_raw_finite_rv_iso_volume :
    ∀ u : (nativeRectangleRawUnitVolume hc T hD L hDF hEF).underlying.obj.domain,
      (unaryProductUnitVolumeObject hc hDF hEF).underlying.obj.value
        (finiteIsoMap (nativeRectangleRawFiniteRVIso hc T hD L hDF hEF) u) =
      (nativeRectangleRawUnitVolume hc T hD L hDF hEF).underlying.obj.value u :=
  native_rectangle_raw_product_map_volume hc T hD L

variable (C : BaseContext M)

def nativeRectangleRawVolumeIso
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 m}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
    {E : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection A D) (hD : IsRVPullback (SpecialTransformations.Section5.carrier D))
    {W : SpecialBijection B E}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P)
    (hDF : (canonicalRVObject hc (pullbackObject D)).volume.FiniteFibres)
    (hEF : (canonicalRVObject hc (pullbackObject E)).volume.FiniteFibres) :
    RVVolumeIso (nativeRectangleRawUnitVolume hc T hD L hDF hEF) (unaryProductUnitVolumeObject hc hDF hEF) :=
  RVVolumeIso.of_preserving_coordinates_full hc C (nativeRectangleRawFiniteRVIso hc T hD L hDF hEF)
    (native_rectangle_raw_finite_rv_iso_volume hc T hD L hDF hEF) (fun _ => rfl)

end IntegrationInACVF.Section7
