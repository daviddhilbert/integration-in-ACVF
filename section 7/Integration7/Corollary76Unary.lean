import Integration7.UnaryContractionGammaVolumeComparison
import Integration7.VFStandardVolumeContractionObjects
import Integration7.NativeVolumeMapRealization
import Integration7.DensityGraphVolumeBijections

/-! Corollary 7.6 in VF dimension one, for arbitrary original volume
forms and the specified actual density-graph contractions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (gammaLogicInput setDefinable pointMapGraph GammaGraphDefinable GammaSetDefinable carrier)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 3200000 in
theorem corollary_7_6_unary
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) (f : VFVolumeBijection U V)
    {σ τ : Equiv.Perm (Fin 1)}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) τ) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (D.base : Set M) 0
        ⟨(U.standardContractionObject hc C Ξ T).extend hCD,
          (U.standardContractionObject_gamma hc C Ξ T).extend hCD⟩
        ⟨(V.standardContractionObject hc C Ξ E).extend hCD,
          (V.standardContractionObject_gamma hc C Ξ E).extend hCD⟩ := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let Z := nativeMixedVolumeDomain hc V.densityGraph.domain
  let fD := f.onDensityGraphs hc C
  let g := nativeMixedVolumeMap hc fD.map
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc fD.map fD.bijective
  have hgΓ : GammaGraphDefinable B (pointMapGraph g) := (gammaLogicInput B).real_map_graph g
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  have hZ : GammaSetDefinable B (carrier Z) := (gammaLogicInput B).real_set _ (setDefinable Z)
  have hm : PreservesVFVolume U.densityGraph.form V.densityGraph.form (rawSpecialMap hc g) := fD.preserves
  obtain ⟨hδ,hε,D,hCD,hCommon⟩ := gamma_unary_contraction_volume_comparison hc C C.uncountable.le
    C.saturated C.small hΞ (Set.Subset.refl _) γ hγ hγ1 A Z hA hZ
    U.densityGraph.finite_labels V.densityGraph.finite_labels g hg hgΓ
    U.densityGraph.form V.densityGraph.form (Fin.last U.arity) (Fin.last V.arity)
    (densityGraph_form_last U) (densityGraph_form_last V) hm T E
    (gamma_program_over_real_base B T.program) (gamma_program_over_real_base B E.program)
  exact ⟨D,hCD,hCommon⟩

end IntegrationInACVF.Section7
