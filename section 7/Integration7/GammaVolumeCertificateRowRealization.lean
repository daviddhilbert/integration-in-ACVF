module

public import Integration7.VolumeCertificateContextRealization
public import Integration7.GammaVolumePresentationGeometry
public import Integration7.GammaVolumeParameterGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A certificate realized on named rows retains its original Gamma
chart. The auxiliary tuple used for the exceptional locus contributes no
new parameters to that chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (GammaGraphDefinable gammaLogicInput)
open SpecialTransformations.Section4 (rvValues)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoCertificateSchema.realizeOnGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : RVVolumeSchemaRow U F.source z) (Q : RVVolumeSchemaRow V F.target z)
    (hU : VolumeObjectGamma U ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hV : VolumeObjectGamma V ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hB : B.real ⊆ (C.base : Set M)) (hzC : Set.range z ⊆ (C.base : Set M)) :
    ∃ (T : BaseContext M) (hCT : (C.base : Set M) ⊆ (T.base : Set M)),
      ∃ e : RVVolumeIso (U.extend hCT) (V.extend hCT),
        e.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ := by
  obtain ⟨T,hCT,e,he⟩ := F.realizeOn hc C z hz P Q hB hzC
  let Bz : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hSource := gamma_essential_volume_domain _ (hU.extend hCT).coordinates
  have hTarget := gamma_essential_volume_domain _ (hV.extend hCT).coordinates
  have hChart := gamma_rv_tuple_relation_specialize sp z hz.1.1.1 F.chart_definable
  let L := gammaLogicInput Bz
  have hR := L.restrict_graph hSource (L.swap_graph
    (L.restrict_graph hTarget (L.swap_graph hChart)))
  refine ⟨T,hCT,e,?_⟩
  apply GammaGraphDefinable.congr hR
  intro x y
  constructor
  · rintro ⟨hx,hy,hxy⟩
    obtain ⟨u,hu,hv⟩ := (he (rvValues x.2) (rvValues y.2)).mp hxy
    exact ⟨u,funext (fun i => Subtype.ext (congrFun hu i)),
      funext (fun i => Subtype.ext (congrFun hv i))⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨(congrArg (fun r => r ∈ _) hu).mp u.property,
      (congrArg (fun r => r ∈ _) hv).mp (finiteIsoMap e.iso u).property,?_⟩
    exact (he (rvValues x.2) (rvValues y.2)).mpr
      ⟨u,congrArg rvValues hu,congrArg rvValues hv⟩

end IntegrationInACVF.Section7
