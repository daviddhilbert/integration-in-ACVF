module

public import Integration7.GammaElementaryBlowupPartitions
public import Integration7.GammaVolumeBlowupRowPromotion
public import Integration7.GammaVolumeObjectGraphPromotion

@[expose] public section

/-! Full original-Gamma geometric blowup data promote to a formula
witness in any genuine containing context. Center algebraicity remains
over the original base; exceptional certificate parameters remain explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_charted_volume_blowup_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (b : VolumeBlowup U V) (hb : b.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩) :
    ∃ H : GammaRVVolumeBlowupSchema F G, H.valid z := by
  obtain ⟨L,hL,PL⟩ := gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz b.locus
    hb.locus.coordinates.domain hb.locus.coordinates hb.locus.density
  obtain ⟨Q,hQ,PQ⟩ := gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz b.complement
    hb.complement.coordinates.domain hb.complement.coordinates hb.complement.density
  obtain ⟨AP⟩ := L.object.realize z hL.1
  have hAdΓ := hb.centerAlgebraic.schema_row z b.locus b.elementary.admissible L PL AP
  obtain ⟨ec,hec⟩ := b.elementary.exists_gamma_canonical_iso hc C hb.locus hb.blown hb.elementary
  let eT := b.targetIso.trans hc C ((ec.symm hc C).coprod hc C (RVVolumeIso.refl hc C b.complement))
  have hT : eT.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩ := hb.target.trans hc C _
    ((hec.symm hc C _).coprod hc C _ (hb.complement.identity_iso hc C))
  exact gamma_volume_blowup_row_promotion hc C hκ hs h00 hreal hgamma z hz F G L Q hF hG hL hQ
    PU PV PL PQ AP b.elementary.admissible hAdΓ b.sourceIso eT hb.source hT

end IntegrationInACVF.Section7
