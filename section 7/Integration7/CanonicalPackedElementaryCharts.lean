import Integration7.PackedEssentialBlowupCharts
import Integration7.GammaEssentialCoordinateGraphs

/-! The canonical elementary chart is the identity on packed labels.
Its full original-Gamma graph therefore follows from that of its actual
essential source, and so does the inverse packed chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem canonical_packed_elementary_chart_value (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (w : (elementaryVolumeObject C U hAd).essential.obj.domain) :
    ((elementaryVolumeBlowup C U hAd).packedEssentialChartMap w).val = w.val := by
  let w0 : (elementaryVolumeObject C U hAd).underlying.obj.domain :=
    ⟨w.val,SpecialTransformations.Section9.rvEssentialLabels_subset _ w.property⟩
  exact congrArg Subtype.val (rvPack_unpack U.underlying.obj.domain (blowupConeSet (C.base : Set M)) w0)

theorem gamma_canonical_packed_elementary_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hAd : BlowupAdmissible U)
    (hW : GammaGraphDefinable B (fun
      (p : Point (M := M) 0 (elementaryVolumeObject C U hAd).underlying.obj.arity)
      (q : Point (M := M) 0 (k+1)) =>
        (elementaryVolumeObject C U hAd).underlying.obj.volume.graph p.2 q.2)) :
    RVMapGamma (elementaryVolumeBlowup C U hAd).packedEssentialChartMap B := by
  apply gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real id)
    (gamma_essential_volume_domain _ hW)
  intro w
  exact canonical_packed_elementary_chart_value C U hAd w

end IntegrationInACVF.Section7
