module

public import Integration7.ActualVolumeBlowupPromotion
public import Integration7.FreeGammaVolumeComparisonPromotion

@[expose] public section

/-! A canonical volume blowup with original-Gamma endpoint charts gives
a formula witness in any containing context. Its admissibility is supplied
over the original Gamma base, rather than inferred from the enlarged real base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

def RVVolumeIso.GammaDefinable {S : Set M}
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (B : Base (M := M)) : Prop :=
  GammaGraphDefinable B
    (fun (x : Point (M := M) 0 U.underlying.obj.arity)
      (y : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.essential.obj.domain, u.val = x.2 ∧ (finiteIsoMap e.iso u).val = y.2)

theorem gamma_volume_blowup_row_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {U V A R : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (L : GammaRVVolumeSchema B p A.underlying.obj.arity k sp)
    (Q : GammaRVVolumeSchema B p R.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (hL : L.valid z) (hQ : Q.valid z)
    (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (PA : RVVolumeSchemaRow A L z) (PR : RVVolumeSchemaRow R Q z)
    (AP : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩
      A.underlying.obj.arity (k+1) (L.object.rowDomain z) (L.object.rowVolume z))
    (hAd : BlowupAdmissible A)
    (hAdΓ : GammaAdmissible AP.toGamma.toGammaRVObject (Fin.last k))
    (eS : RVVolumeIso U (A.coprod R))
    (eT : RVVolumeIso V ((elementaryVolumeObject C A hAd).coprod R))
    (hSΓ : eS.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩)
    (hTΓ : eT.GammaDefinable ⟨B.real ∪ Set.range z,B.gamma⟩) :
    ∃ H : GammaRVVolumeBlowupSchema F G, H.valid z := by
  obtain ⟨NAd,hNAd⟩ := L.exists_admissibility_bound hκ hs h00 hreal hgamma z hL AP hAdΓ
  obtain ⟨NE,hNE⟩ := L.exists_valid_elementary_bound hκ hs h00 hreal hgamma z hL AP hAdΓ
  obtain ⟨NS,hNS⟩ := L.exists_valid_coprod_bound hκ hs hreal hgamma Q z hL hQ
  obtain ⟨NT,hNT⟩ := (L.elementaryFormula.withBound NE).exists_valid_coprod_bound
    hκ hs hreal hgamma Q z hNE hQ
  have hNT' : ((L.elementaryFormula.coprodFormula Q).withBound NT).valid z := hNT
  have PS : RVVolumeSchemaRow (A.coprod R) ((L.coprodFormula Q).withBound NS) z :=
    (PA.coprod PR hz).congr (GammaRVVolumeSchema.sameRow_symm ((L.coprodFormula Q).withBound_sameRow NS z hz))
  let E := elementaryVolumeObject C A hAd
  have PE : RVVolumeSchemaRow E L.elementaryFormula z := PA.elementary C hL hAd
  have PT : RVVolumeSchemaRow (E.coprod R) ((L.elementaryFormula.coprodFormula Q).withBound NT) z :=
    (PE.coprod PR hz).congr
      (GammaRVVolumeSchema.sameRow_symm ((L.elementaryFormula.coprodFormula Q).withBound_sameRow NT z hz))
  obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma
    C z hz F ((L.coprodFormula Q).withBound NS) hF hNS PU PS eS hSΓ
  obtain ⟨J,hJS,hJT,hJ,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma
    C z hz G ((L.elementaryFormula.coprodFormula Q).withBound NT) hG hNT' PV PT eT hTΓ
  let H : GammaRVVolumeBlowupSchema F G := {
    centerArity := A.underlying.obj.arity
    remainderArity := R.underlying.obj.arity
    center := L
    remainder := Q
    admissibilityBound := NAd
    sourceChart := I
    resultChart := J }
  refine ⟨H,hF,hG,hL,hQ,hNAd,hI,hJ,?_,?_,?_,?_⟩
  · rw [hIS]
    exact F.sameRow_refl z hz
  · rw [hIT]
    exact (L.coprodFormula Q).withBound_sameRow NS z hz
  · rw [hJS]
    exact G.sameRow_refl z hz
  · rw [hJT]
    exact (L.elementaryFormula.coprodFormula Q).withBound_sameRow NT z hz

end IntegrationInACVF.Section7
