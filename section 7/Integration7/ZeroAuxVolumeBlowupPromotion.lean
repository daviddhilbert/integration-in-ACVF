import Integration7.ActualVolumeObjectPromotion
import Integration7.ZeroAuxVolumeComparisonPromotion
import Integration7.ActualVolumeAdmissibilityPromotion
import Integration7.VolumeBlowupSchemaRealization
import Integration7.ElementaryBlowupIsomorphism

/-! Actual blowups over the named term context promote with no
additional exception parameters in either splitting comparison. The
canonical elementary comparison is the checked actual volume theorem. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_blowup_promotion_no_auxiliary {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (b : VolumeBlowup U V) : ∃ H : GammaRVVolumeBlowupSchema F G, H.valid z ∧ H.NoAuxiliary := by
  obtain ⟨A,hA,PA⟩ := gamma_volume_actual_object_promotion hc C hκ hs hreal hgamma z hz hBase b.locus
  obtain ⟨R,hR,PR⟩ := gamma_volume_actual_object_promotion hc C hκ hs hreal hgamma z hz hBase b.complement
  obtain ⟨AP⟩ := A.object.realize z hA.1
  have hAd := PA.gammaAdmissibleInTermContext hc C hBase AP b.elementary.admissible
  obtain ⟨NAd,hNAd⟩ := A.exists_admissibility_bound hκ hs h00 hreal hgamma z hA AP hAd
  obtain ⟨NE,hNE⟩ := A.exists_valid_elementary_bound hκ hs h00 hreal hgamma z hA AP hAd
  obtain ⟨NS,hNS⟩ := A.exists_valid_coprod_bound hκ hs hreal hgamma R z hA hR
  obtain ⟨NT,hNT⟩ := (A.elementaryFormula.withBound NE).exists_valid_coprod_bound
    hκ hs hreal hgamma R z hNE hR
  have hNT' : ((A.elementaryFormula.coprodFormula R).withBound NT).valid z := hNT
  have PS : RVVolumeSchemaRow (b.locus.coprod b.complement) ((A.coprodFormula R).withBound NS) z :=
    (PA.coprod PR hz).congr (GammaRVVolumeSchema.sameRow_symm ((A.coprodFormula R).withBound_sameRow NS z hz))
  let E := elementaryVolumeObject C b.locus b.elementary.admissible
  have PE : RVVolumeSchemaRow E A.elementaryFormula z := PA.elementary C hA b.elementary.admissible
  have PT : RVVolumeSchemaRow (E.coprod b.complement) ((A.elementaryFormula.coprodFormula R).withBound NT) z :=
    (PE.coprod PR hz).congr
      (GammaRVVolumeSchema.sameRow_symm ((A.elementaryFormula.coprodFormula R).withBound_sameRow NT z hz))
  let eE := elementaryBlowupIso hc C (RVVolumeIso.refl hc C b.locus)
    b.elementary (elementaryVolumeBlowup C b.locus b.elementary.admissible)
  let eT := b.targetIso.trans hc C (eE.coprod hc C (RVVolumeIso.refl hc C b.complement))
  obtain ⟨I,hIQ,hIS,hIT,hI,_⟩ := gamma_volume_comparison_promotion_no_auxiliary hc C hκ hs hreal hgamma
    z hz hBase F ((A.coprodFormula R).withBound NS) hF hNS PU PS b.sourceIso
  obtain ⟨J,hJQ,hJS,hJT,hJ,_⟩ := gamma_volume_comparison_promotion_no_auxiliary hc C hκ hs hreal hgamma
    z hz hBase G ((A.elementaryFormula.coprodFormula R).withBound NT) hG hNT' PV PT eT
  let H : GammaRVVolumeBlowupSchema F G := {
    centerArity := b.locus.underlying.obj.arity
    remainderArity := b.complement.underlying.obj.arity
    center := A
    remainder := R
    admissibilityBound := NAd
    sourceChart := I
    resultChart := J }
  refine ⟨H,⟨hF,hG,hA,hR,hNAd,hI,hJ,?_,?_,?_,?_⟩,hIQ,hJQ⟩
  · rw [hIS]
    exact F.sameRow_refl z hz
  · rw [hIT]
    exact (A.coprodFormula R).withBound_sameRow NS z hz
  · rw [hJS]
    exact G.sameRow_refl z hz
  · rw [hJT]
    exact (A.elementaryFormula.coprodFormula R).withBound_sameRow NT z hz

end IntegrationInACVF.Section7
