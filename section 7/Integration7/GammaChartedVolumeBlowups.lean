import Integration7.FullPackedBlowupCharts
import Integration7.GammaVolumeCoproductCoherence
import Integration7.GammaVolumeCoproductCharts
import Integration7.IteratedVolumeBlowups
import Integration7.GammaVolumeAlgebraicCenters

/-! Original-Gamma certificates for the existing actual volume blowup.
The full elementary chart is retained, including degenerate labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

structure VolumeBlowup.GammaDefinable {S : Set M}
    {U W : PositiveRVVolumeObject (M := M) S k} (b : VolumeBlowup U W) (B : Base (M := M)) : Prop where
  locus : VolumeObjectGamma b.locus B
  complement : VolumeObjectGamma b.complement B
  blown : VolumeObjectGamma b.blownLocus B
  elementary : RVMapGamma b.elementary.packedChartMap B
  centerAlgebraic : GammaBlowupCenter b.locus B
  source : b.sourceIso.GammaDefinable B
  target : b.targetIso.GammaDefinable B

theorem VolumeBlowup.GammaDefinable.on_coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A D : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup A D) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hA : VolumeObjectGamma A B) (hD : VolumeObjectGamma D B) (hR : VolumeObjectGamma R B)
    (hb : RVMapGamma b.packedChartMap B) (hCenter : GammaBlowupCenter A B) :
    (VolumeBlowup.on_coprod hc C b R).GammaDefinable B :=
  ⟨hA,hR,hD,hb,hCenter,(hA.coprod hR).identity_iso hc C,(hD.coprod hR).identity_iso hc C⟩

theorem VolumeBlowup.GammaDefinable.transport
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' W W' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {b : VolumeBlowup U W} (hb : b.GammaDefinable B)
    (f : RVVolumeIso U' U) (g : RVVolumeIso W' W)
    (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) :
    (b.transport hc C f g).GammaDefinable B :=
  ⟨hb.locus,hb.complement,hb.blown,hb.elementary,hb.centerAlgebraic,
    hf.trans hc C B hb.source,hg.trans hc C B hb.target⟩

theorem VolumeObjectGamma.canonical_blowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A R : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hA : VolumeObjectGamma A B) (hR : VolumeObjectGamma R B) (hAd : BlowupAdmissible A)
    (hCenter : GammaBlowupCenter A B) :
    (VolumeBlowup.on_coprod hc C (elementaryVolumeBlowup C A hAd) R).GammaDefinable B :=
  VolumeBlowup.GammaDefinable.on_coprod hc C _ R hA (hA.elementary_canonical hc C A hAd) hR
    (gamma_canonical_full_packed_chart hc C A hAd hA) hCenter

end IntegrationInACVF.Section7
