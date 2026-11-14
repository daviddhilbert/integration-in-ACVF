import Integration7.GammaElementaryVolumeGraphs
import Integration7.GammaRVMapPreimages
import Integration7.GammaRVScalarMapGraphs
import Integration7.ElementaryBlowupRestriction

/-! Full packed elementary charts track all labels, including degenerate
ones. Gamma full charts restrict to Gamma essential charts and cuts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7.ElementaryBlowup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ} {B : Base (M := M)}
variable {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)

def packedChartMap : Map W.underlying.obj.domain
    (rvProductDomain U.underlying.obj.domain (blowupConeSet S)) :=
  (rvPack U.underlying.obj.domain (blowupConeSet S)).toImage.comp b.chartMap

theorem packedChartMap_bijective : Function.Bijective b.packedChartMap :=
  (rvPackToImage_bijective _ _).comp b.chartMap_bijective

theorem gamma_essential_packed_chart (hW : VolumeObjectGamma W B)
    (hFull : RVMapGamma b.packedChartMap B) : RVMapGamma b.packedEssentialChartMap B :=
  (hFull.restrict (rvEssentialLabels_subset W.underlying.obj)
    (gamma_essential_volume_domain W hW.coordinates)).congr (fun _ => rfl)

theorem gamma_projection (hc : CanonicalStructure.IsCanonical (M := M))
    (hFull : RVMapGamma b.packedChartMap B) : RVMapGamma b.projection B := by
  have h := (hFull.congr (g := b.packedChartMap.toUniv) (fun _ => rfl)).select hc
    (Fin.castAdd 1 : Fin U.underlying.obj.arity → Fin (U.underlying.obj.arity+1))
  apply h.congr
  intro w
  funext i
  exact Fin.append_left (b.chartMap w).val.1 (b.chartMap w).val.2 i

theorem gamma_source_preimage (hc : CanonicalStructure.IsCanonical (M := M))
    (hFull : RVMapGamma b.packedChartMap B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    GammaSetDefinable B {p : Point (M := M) 0 W.underlying.obj.arity | p.2 ∈ (b.sourcePreimage A).carrier} :=
  (b.gamma_projection hc hFull).preimage A hAΓ

theorem gamma_restricted_packed_chart (hc : CanonicalStructure.IsCanonical (M := M))
    (hFull : RVMapGamma b.packedChartMap B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    RVMapGamma (b.restrict A hA).packedChartMap B :=
  (hFull.restrict (b.sourcePreimage_subset A) (b.gamma_source_preimage hc hFull A hAΓ)).congr (fun _ => rfl)

end IntegrationInACVF.Section7.ElementaryBlowup

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_canonical_full_packed_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (hU : VolumeObjectGamma U B) : RVMapGamma (elementaryVolumeBlowup C U hAd).packedChartMap B := by
  apply gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real id)
    (gamma_elementary_volume_coordinates hc C U hAd hU.coordinates).domain
  intro w
  exact congrArg Subtype.val (rvPack_unpack U.underlying.obj.domain (blowupConeSet (C.base : Set M)) w)

end IntegrationInACVF.Section7
