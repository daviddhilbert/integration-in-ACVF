import Integration7.FieldBaseUnaryIntegralBijections
import Integration7.NativeRVGraphVolumeRefinements

/-! A unary source with a literal retained density can be integrated
using its actual original-label contraction. Passing through its density
graph changes neither the resulting common-blowup class nor the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

set_option maxHeartbeats 1600000 in
theorem unary_field_integral_retained_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) 1 a)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ q, ω.value q=q.val.2 δ)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (T : StandardContraction A (Equiv.refl _)) :
    positiveVolumeBlowupClass (k := 0) hc C (rawStandardVolumeObject hc C Ξ A hfin δ hδ T) =
      unaryFieldVolumeIntegral hc C Ξ FBase (nativeMixedVFVolumeObject hc A hfin ω) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let W := nativeMixedVFVolumeObject hc A hfin ω
  let B := nativeMixedVolumeDomain hc W.densityGraph.domain
  let e := volumeDensityGraphBijection hc C W
  let g : Map A B := nativeMixedVolumeMap hc e.map
  let E := unaryFieldVolumeContraction hc C Ξ FBase W
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc e.map e.bijective
  have hm : PreservesVFVolume ω W.densityGraph.form (rawSpecialMap hc g) := e.preserves
  obtain ⟨hα,hβ,D,hCD,h⟩ := gamma_unary_raw_finite_volume_comparison hc C C (Set.Subset.refl _)
    C.uncountable.le C.saturated C.small hΞ (Set.Subset.refl _) γ hγ hγ1
    A B ((gammaLogicInput G).real_set _ (setDefinable A)) ((gammaLogicInput G).real_set _ (setDefinable B))
    hfin W.densityGraph.finite_labels g hg ((gammaLogicInput G).real_map_graph g)
    ω W.densityGraph.form δ (Fin.last a) hω (densityGraph_form_last W) hm T E
    (gamma_program_over_real_base G T.program) (gamma_program_over_real_base G E.program)
  let U := rawStandardVolumeObject hc C Ξ A hfin δ hδ T
  let V := rawStandardVolumeObject hc C Ξ B W.densityGraph.finite_labels (Fin.last a)
    (unary_density_graph_label_nonzero W) E
  have H : CommonContextVolumeEquivalent G C
      ⟨U,raw_standard_volume_object_gamma hc C Ξ A _ _ _ T⟩
      ⟨V,raw_standard_volume_object_gamma hc C Ξ B _ _ _ E⟩ := ⟨D,hCD,h⟩
  exact (positiveVolumeBlowupClass_eq_iff hc C).mpr ((H.descend hc C hNames).toOrdinary hc C G)
end IntegrationInACVF.Section7
