import Integration7.GammaNamedLiftKernel
import Integration7.PositiveVolumeLiftSurjectivity
import Integration7.GammaSpecialCommonNames
import Section5.GammaInvariantLogic

/-! Gamma-named surjectivity of the volume lift. Every positive VF volume
object with a Gamma density graph over a VF-Gamma-generated base `G` is
isomorphic, through an almost-everywhere VF volume isomorphism with a Gamma
graph, to the lift of a Gamma RV volume object. The Gamma special bijection
comes from the predecessor's Gamma Corollary 5.6 realized over a code set
containing the common names. No transport input is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n m k : ℕ}

theorem gamma_special_bijection_cast_source {S : Set M} {l : ℕ} {A A' : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : SpecialBijection A B) (h : A = A')
    (hT : GammaChainDefinable G T.chain) :
    ∃ T' : SpecialBijection A' B, GammaChainDefinable G T'.chain := by
  subst h
  exact ⟨T,hT⟩

/-- Gamma Corollary 5.6 realized over a code context containing the common names. -/
theorem gamma_special_pullback_exists (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase G)
    (A : DefSet (M := M) (C.base : Set M) n m) (hA : GammaSetDefinable G (carrier A)) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) (C.base : Set M) n r, ∃ T : SpecialBijection A B,
      GammaChainDefinable G T.chain ∧ IsRVPullback (carrier B) := by
  obtain ⟨r,D,⟨T⟩,hDP⟩ := Paper.corollary_5_6_gamma C.saturated C.model00 G
    ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) (generatedBaseVFField hGenerated) (carrier A) hA
  let T' := gammaSpecialPresentation T.special T.invariant_graphs hNames
  have hsrc : gammaNativePresentation T.source (T.invariant_graphs.source G T.special.chain) hNames = A :=
    defSet_eq_of_carrier_eq T.source_eq
  obtain ⟨T'',hT''⟩ := gamma_special_bijection_cast_source T' hsrc
    (gamma_chain_presentation_gamma T.special.chain T.invariant_graphs hNames)
  refine ⟨r,_,T'',hT'',?_⟩
  change IsRVPullback (carrier T.target)
  rw [T.target_eq]
  exact hDP

namespace GammaNamed

theorem gamma_volume_lift_iso_exists (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase G)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (hU : VFVolumeObjectGamma U G) :
    ∃ P : GammaVolumeObjects G (C.base : Set M) k,
      ∃ e : VFVolumeIso U (rvVolumeLift P.val), e.GammaDefinable G := by
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  obtain ⟨b,B,T,hT,hBP⟩ := gamma_special_pullback_exists C hGC hNames hGenerated A hU.densityGraph
  have hB : GammaSetDefinable G (carrier B) := GammaChainDefinable.target G T.chain hT
  let δ := Fin.last U.arity
  have hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := by
    intro p
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact U.densityGraph.form.nonzero ⟨p.val,p.property⟩
      ((densityGraph_form_last U ⟨p.val,p.property⟩).trans hz)
  have hfinB := special_target_finite_labels C ∅ T U.densityGraph.finite_labels
  have hBF := special_pullback_volume_finite C ∅ T hBP U.densityGraph.finite_labels
  let ε := suffixIndex (special_chain_rvArity_le T.chain) δ
  have hε := special_retained_density_nonzero T δ hδ
  let P := pullbackCoordinateGammaObject hc C hGC B hB hBF ε hε
  let ψ := rawPullbackVolumeForm hc B hBP hBF ε hε
  let W := nativeMixedVFVolumeObject hc B hfinB ψ
  have hDensity : ∀ p, U.densityGraph.form.value p = ψ.value (rawSpecialMap hc T.toMap p) := by
    intro p
    rw [densityGraph_form_last,rawPullbackVolumeForm_density]
    exact (special_oldLabels T ⟨p.val,p.property⟩ δ).symm
  let f : VFVolumeBijection U.densityGraph W := ⟨rawSpecialMap hc T.toMap,T.bijective,
    (special_preserves_volume hc C (Nat.zero_lt_succ k) T U.densityGraph.form ψ hDensity).1⟩
  let g : VFVolumeBijection W (rvVolumeLift P.val) := ⟨rawPullbackVolumeLiftMap hc B hBP,
    rawPullbackVolumeLiftMap_bijective hc B hBP,rawPullbackVolumeLiftMap_preserves hc C B hBP hBF ε hε⟩
  let h := (volumeDensityGraphBijection hc C U).trans hc C (f.trans hc C g)
  refine ⟨P,VFVolumeIso.of_bijection h,hU.domain,
    gamma_rv_lift_carrier hc C hGC P.val P.property,?_⟩
  -- the three graphs: density graph append, special bijection, canonical pullback lift
  have L := gammaLogicInput G
  have hAppend : GammaGraphDefinable G (vfMixedMapGraph (volumeDensityGraphBijection hc C U).map) := by
    apply GammaGraphDefinable.congr (L.swap_graph hU.projection_graph)
    intro p q
    constructor
    · rintro ⟨hq,rfl⟩
      obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form q).mp hq
      exact ⟨⟨_,hq0⟩,rfl,hqe.symm⟩
    · rintro ⟨u,rfl,rfl⟩
      refine ⟨((appendDensityMap U.form).toImage u).property,?_⟩
      change u.val = ((appendDensityMap U.form u).val.1,(appendDensityMap U.form u).val.2 ∘ Fin.castAdd 1)
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
  have hSpecial : GammaGraphDefinable G (vfMixedMapGraph f.map) :=
    vf_mixed_map_graph_raw_special hc T.toMap (GammaChainDefinable.graph L T.chain hT)
  have hCanon : GammaGraphDefinable G (vfMixedMapGraph g.map) := by
    have hc' := GammaPrimitiveDefinable.graph L (Primitive.canonical B) hB
    apply GammaGraphDefinable.congr hc'
    intro p q
    constructor
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
    · rintro ⟨u,rfl,rfl⟩
      exact ⟨⟨u.val,u.property⟩,rfl,rfl⟩
  apply GammaGraphDefinable.congr (L.comp_graph hAppend (L.comp_graph hSpecial hCanon))
  intro p q
  constructor
  · rintro ⟨z,⟨u,rfl,rfl⟩,z',⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩
    have hv' : v = (volumeDensityGraphBijection hc C U).map u := Subtype.ext hv
    have hw' : w = f.map v := Subtype.ext hw
    subst hv' hw'
    exact ⟨u,rfl,rfl⟩
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨_,⟨u,rfl,rfl⟩,_,⟨_,rfl,rfl⟩,⟨_,rfl,rfl⟩⟩

end GammaNamed
end IntegrationInACVF.Section7
