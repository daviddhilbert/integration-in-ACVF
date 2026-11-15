import Integration7.FieldBaseUnaryVolumeIntegrals
import Integration7.NativeVolumeMapRealization

/-! The field-base unary integral respects genuine VF volume bijections.
The proof compares the two actual density-graph contractions directly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 1600000 in
theorem unary_field_volume_integral_bijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) (f : VFVolumeBijection U V) :
    unaryFieldVolumeIntegral hc C Ξ FBase U = unaryFieldVolumeIntegral hc C Ξ FBase V := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let B := nativeMixedVolumeDomain hc V.densityGraph.domain
  let e := ((volumeDensityGraphBijection hc C U).symm hc C).trans hc C (f.trans hc C (volumeDensityGraphBijection hc C V))
  let g : Map A B := nativeMixedVolumeMap hc e.map
  let T := unaryFieldVolumeContraction hc C Ξ FBase U
  let E := unaryFieldVolumeContraction hc C Ξ FBase V
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc e.map e.bijective
  have hm : PreservesVFVolume U.densityGraph.form V.densityGraph.form (rawSpecialMap hc g) := e.preserves
  obtain ⟨hδ,hε,D,hCD,h⟩ := gamma_unary_raw_finite_volume_comparison hc C C (Set.Subset.refl _)
    C.uncountable.le C.saturated C.small hΞ (Set.Subset.refl _) γ hγ hγ1
    A B ((gammaLogicInput G).real_set _ (setDefinable A)) ((gammaLogicInput G).real_set _ (setDefinable B))
    U.densityGraph.finite_labels V.densityGraph.finite_labels g hg ((gammaLogicInput G).real_map_graph g)
    U.densityGraph.form V.densityGraph.form (Fin.last U.arity) (Fin.last V.arity)
    (densityGraph_form_last U) (densityGraph_form_last V) hm T E
    (gamma_program_over_real_base G T.program) (gamma_program_over_real_base G E.program)
  let P := rawStandardVolumeObject hc C Ξ A U.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero U) T
  let Q := rawStandardVolumeObject hc C Ξ B V.densityGraph.finite_labels
    (Fin.last V.arity) (unary_density_graph_label_nonzero V) E
  have H : CommonContextVolumeEquivalent G C
      ⟨P,raw_standard_volume_object_gamma hc C Ξ A _ _ _ T⟩
      ⟨Q,raw_standard_volume_object_gamma hc C Ξ B _ _ _ E⟩ := ⟨D,hCD,h⟩
  exact (positiveVolumeBlowupClass_eq_iff hc C).mpr ((H.descend hc C hNames).toOrdinary hc C G)
end IntegrationInACVF.Section7
