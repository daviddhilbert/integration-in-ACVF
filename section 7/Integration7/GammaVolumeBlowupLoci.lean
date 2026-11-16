module

public import Integration7.GammaChartedVolumeBlowups
public import Integration7.GammaCoproductVolumeComplements
public import Integration7.GammaVolumeComplementImages
public import Integration7.VolumeBlowupLoci

@[expose] public section

/-! The actual locus, its comparison and its complement in a Gamma
volume blowup retain the original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7.VolumeBlowup.GammaDefinable
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
variable {b : VolumeBlowup U W} (hb : b.GammaDefinable B)
include hb

theorem gamma_source_locus :
    GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ (b.sourceLocus hc C).carrier} := by
  exact gamma_volume_subobject_image (b.sourceIso.symm hc C) (hb.source.symm hc C B)
    (coprodEssentialLeftMap b.locus b.complement).image
    (by rintro x ⟨u,rfl⟩; exact (coprodEssentialLeftMap b.locus b.complement u).property)
    (gamma_coprod_essential_left_map hc b.locus b.complement hb.locus).image

theorem gamma_source_locus_chart : (b.sourceLocusChart hc C).GammaDefinable B := by
  have hL := gamma_volume_coprod_left_image_iso hc C b.locus b.complement hb.locus
  have hI := gamma_volume_subobject_iso hc C (b.sourceIso.symm hc C) (hb.source.symm hc C B)
    (hb.locus.coprod hb.complement) (coprodEssentialLeftMap b.locus b.complement).image
    (by rintro x ⟨u,rfl⟩; exact (coprodEssentialLeftMap b.locus b.complement u).property)
    (gamma_coprod_essential_left_map hc b.locus b.complement hb.locus).image
  exact hL.trans hc C B hI

theorem gamma_source_complement_iso : (b.sourceComplementIso hc C).GammaDefinable B := by
  have hI := gamma_volume_complement_image_iso hc C (b.sourceIso.symm hc C) (hb.source.symm hc C B)
    (hb.locus.coprod hb.complement) (coprodEssentialLeftMap b.locus b.complement).image
    (by rintro x ⟨u,rfl⟩; exact (coprodEssentialLeftMap b.locus b.complement u).property)
    (gamma_coprod_essential_left_map hc b.locus b.complement hb.locus).image
  exact (hI.symm hc C B).trans hc C B
    (gamma_volume_coprod_left_complement_iso hc C b.locus b.complement hb.locus hb.complement)

theorem gamma_result_on_source_locus : (b.resultOnSourceLocus hc C).GammaDefinable B :=
  hb.target.trans hc C B ((hb.blown.identity_iso hc C).coprod hc C B
    ((hb.gamma_source_complement_iso hc C).symm hc C B))

end IntegrationInACVF.Section7.VolumeBlowup.GammaDefinable
