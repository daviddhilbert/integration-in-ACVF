module

public import Integration7.GammaBlowupCommonNameAdmissibility
public import Integration7.FullPackedBlowupCharts

@[expose] public section

/-! Rebase the full elementary chart, including degenerate labels, and
its original-Gamma algebraic center over the actual common-name base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S T : Set M} {k : ℕ}

def elementaryChartOverCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (hNames : commonRealNames G ⊆ T)
    (U W : GammaVolumeObjects G S k) (b : ElementaryBlowup U.val W.val)
    (hb : RVMapGamma b.packedChartMap G) :
    Map (W.overCommonNames hc hNames).val.underlying.obj.domain
      ((U.overCommonNames hc hNames).val.underlying.obj.domain.prod (blowupConeSet T)) := by
  let UC := (U.overCommonNames hc hNames).val
  let WC := (W.overCommonNames hc hNames).val
  let F : Map WC.underlying.obj.domain (rvProductDomain UC.underlying.obj.domain (blowupConeSet T)) :=
    (gammaRVMapRebase hc hNames b.packedChartMap hb).corestrict
      (fun w => (b.packedChartMap ⟨w.val,w.property⟩).property)
  let g := (rvUnpack UC.underlying.obj.domain (blowupConeSet T)).comp F
  have hValue (w : WC.underlying.obj.domain) : (g w).val = (b.chartMap ⟨w.val,w.property⟩).val :=
    congrArg Subtype.val (rvUnpack_pack UC.underlying.obj.domain (blowupConeSet T)
      ⟨(b.chartMap ⟨w.val,w.property⟩).val,(b.chartMap ⟨w.val,w.property⟩).property⟩)
  refine ⟨fun w => ⟨(b.chartMap ⟨w.val,w.property⟩).val,(b.chartMap ⟨w.val,w.property⟩).property⟩,?_⟩
  apply g.graph_definable.congr _ _
  intro x y
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨u,hu,(hValue u).symm.trans hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨u,hu,(hValue u).trans hv⟩

def elementaryBlowupOverCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (hNames : commonRealNames G ⊆ T)
    (U W : GammaVolumeObjects G S k) (b : ElementaryBlowup U.val W.val)
    (hb : RVMapGamma b.packedChartMap G) (hCenter : GammaBlowupCenter U.val G) :
    ElementaryBlowup (U.overCommonNames hc hNames).val (W.overCommonNames hc hNames).val where
  admissible := gamma_blowup_admissible_over_common_names hc hNames U b.admissible hCenter
  chartMap := elementaryChartOverCommonNames hc hNames U W b hb
  chartMap_bijective := b.chartMap_bijective
  head := b.head
  last := b.last
  volume := b.volume

theorem gamma_elementary_blowup_over_common_names_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (hNames : commonRealNames G ⊆ T)
    (U W : GammaVolumeObjects G S k) (b : ElementaryBlowup U.val W.val)
    (hb : RVMapGamma b.packedChartMap G) (hCenter : GammaBlowupCenter U.val G) :
    RVMapGamma (elementaryBlowupOverCommonNames hc hNames U W b hb hCenter).packedChartMap G := hb

end IntegrationInACVF.Section7
