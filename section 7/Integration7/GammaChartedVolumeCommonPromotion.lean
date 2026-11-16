module

public import Integration7.GammaChartedVolumeBlowupPromotion
public import Integration7.GammaVolumeBlowupEquivalence
public import Integration7.GammaVolumeChainSchemata

@[expose] public section

/-! Original-Gamma finite geometric chains and common refinements have
formula witnesses in any genuine containing context. These certificates
may have auxiliary exceptional-set parameters; no auxiliary-free conclusion
or named-context equality is asserted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_charted_volume_chain_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {U V : GammaVolumeObjects ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k} {r : ℕ}
    (F : GammaRVVolumeSchema B p U.val.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.val.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U.val F z) (PV : RVVolumeSchemaRow V.val G z)
    (b : GammaIteratedVolumeBlowup ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k r U V) :
    ∃ H : GammaVolumeChainSchema F G r, H.valid z := by
  cases b with
  | refl =>
    obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma C
      z hz F G hF hG PU PV (RVVolumeIso.refl hc C _) (U.property.identity_iso hc C)
    refine ⟨.iso I,hI,?_,?_⟩
    · rw [hIS]
      exact F.sameRow_refl z hz
    · rw [hIT]
      exact G.sameRow_refl z hz
  | @step n U V W head rest =>
    obtain ⟨b,hb⟩ := head
    obtain ⟨K,hK,PK⟩ := gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz V.val
      V.property.coordinates.domain V.property.coordinates V.property.density
    obtain ⟨head,hhead⟩ := gamma_charted_volume_blowup_promotion hc C hκ hs h00 hreal hgamma
      z hz F K hF hK PU PK b hb
    obtain ⟨tail,htail⟩ := gamma_charted_volume_chain_promotion hc C hκ hs h00 hreal hgamma
      z hz K G hK hG PK PV rest
    exact ⟨.step K head tail,hK,hhead,htail⟩
termination_by r

theorem gamma_charted_volume_common_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    {U V : GammaVolumeObjects ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.val.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.val.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U.val F z) (PV : RVVolumeSchemaRow V.val G z)
    (h : GammaVolumeBlowupEquivalent ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) k U V) :
    ∃ H : GammaVolumeCommonSchema F G, H.valid z := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := h
  obtain ⟨L,hL,PL⟩ := gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz U'.val
    U'.property.coordinates.domain U'.property.coordinates U'.property.density
  obtain ⟨R,hR,PR⟩ := gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz V'.val
    V'.property.coordinates.domain V'.property.coordinates V'.property.density
  obtain ⟨lc,hlc⟩ := gamma_charted_volume_chain_promotion hc C hκ hs h00 hreal hgamma z hz
    F L hF hL PU PL hU
  obtain ⟨rc,hrc⟩ := gamma_charted_volume_chain_promotion hc C hκ hs h00 hreal hgamma z hz
    G R hG hR PV PR hV
  obtain ⟨I,hIS,hIT,hI,_⟩ := gamma_volume_row_comparison_promotion_free hc hκ hs hreal hgamma C
    z hz L R hL hR PL PR e he
  let H : GammaVolumeCommonSchema F G := {
    leftArity := U'.val.underlying.obj.arity
    rightArity := V'.val.underlying.obj.arity
    leftObject := L
    rightObject := R
    leftLength := m
    rightLength := n
    leftChain := lc
    rightChain := rc
    comparison := I }
  refine ⟨H,hF,hG,hL,hR,hlc,hrc,hI,?_,?_⟩
  · rw [hIS]
    exact L.sameRow_refl z hz
  · rw [hIT]
    exact R.sameRow_refl z hz

end IntegrationInACVF.Section7
