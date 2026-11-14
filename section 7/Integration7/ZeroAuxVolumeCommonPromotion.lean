import Integration7.ZeroAuxVolumeBlowupPromotion
import Integration7.GammaVolumeChainSchemata

/-! Actual finite chains and common forward blowups over the named
term context promote with every exception parameter block empty. This
strengthens the existing promotion conclusion for formula preparation. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volume_chain_promotion_no_auxiliary {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {r : ℕ}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (b : IteratedVolumeBlowup r U V) : ∃ H : GammaVolumeChainSchema F G r, H.valid z ∧ H.NoAuxiliary := by
  cases b with
  | refl =>
    obtain ⟨I,hIQ,hIS,hIT,hI,_⟩ := gamma_volume_comparison_promotion_no_auxiliary hc C hκ hs hreal hgamma
      z hz hBase F G hF hG PU PV (RVVolumeIso.refl hc C _)
    refine ⟨.iso I,⟨hI,?_,?_⟩,hIQ⟩
    · rw [hIS]
      exact F.sameRow_refl z hz
    · rw [hIT]
      exact G.sameRow_refl z hz
  | step hb rest =>
    let b := hb.some
    obtain ⟨W,hW,PW⟩ := gamma_volume_actual_object_promotion hc C hκ hs hreal hgamma z hz hBase _
    obtain ⟨head,hhead,hHeadAux⟩ := gamma_volume_blowup_promotion_no_auxiliary hc C hκ hs h00 hreal hgamma
      z hz hBase F W hF hW PU PW b
    obtain ⟨tail,htail,hTailAux⟩ := gamma_volume_chain_promotion_no_auxiliary hc C hκ hs h00 hreal hgamma
      z hz hBase W G hW hG PW PV rest
    exact ⟨.step W head tail,⟨hW,hhead,htail⟩,hHeadAux,hTailAux⟩
termination_by r

theorem gamma_volume_common_promotion_no_auxiliary {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp)
    (G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp)
    (hF : F.valid z) (hG : G.valid z) (PU : RVVolumeSchemaRow U F z) (PV : RVVolumeSchemaRow V G z)
    (h : VolumeBlowupEquivalent U V) : ∃ H : GammaVolumeCommonSchema F G, H.valid z ∧ H.NoAuxiliary := by
  obtain ⟨m,n,U',V',hU,hV,⟨e⟩⟩ := h
  obtain ⟨L,hL,PL⟩ := gamma_volume_actual_object_promotion hc C hκ hs hreal hgamma z hz hBase U'
  obtain ⟨R,hR,PR⟩ := gamma_volume_actual_object_promotion hc C hκ hs hreal hgamma z hz hBase V'
  obtain ⟨lc,hlc,hlcAux⟩ := gamma_volume_chain_promotion_no_auxiliary hc C hκ hs h00 hreal hgamma
    z hz hBase F L hF hL PU PL hU
  obtain ⟨rc,hrc,hrcAux⟩ := gamma_volume_chain_promotion_no_auxiliary hc C hκ hs h00 hreal hgamma
    z hz hBase G R hG hR PV PR hV
  obtain ⟨I,hIQ,hIS,hIT,hI,_⟩ := gamma_volume_comparison_promotion_no_auxiliary hc C hκ hs hreal hgamma
    z hz hBase L R hL hR PL PR e
  let H : GammaVolumeCommonSchema F G := {
    leftArity := U'.underlying.obj.arity
    rightArity := V'.underlying.obj.arity
    leftObject := L
    rightObject := R
    leftLength := m
    rightLength := n
    leftChain := lc
    rightChain := rc
    comparison := I }
  refine ⟨H,⟨hF,hG,hL,hR,hlc,hrc,hI,?_,?_⟩,hlcAux,hrcAux,hIQ⟩
  · rw [hIS]
    exact L.sameRow_refl z hz
  · rw [hIT]
    exact R.sameRow_refl z hz

end IntegrationInACVF.Section7
