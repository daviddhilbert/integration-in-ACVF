import Integration7.FieldBaseUnaryIntegralBijections
import Integration7.VFVolumeObjectLabelCuts
import Integration7.UnaryRawSelectedVolumeCharts
import Integration7.SelectedStandardBinaryVolumePartitions

/-! Complementary old-label cuts are additive for genuine unary VF
volume integration, including the zero-old-coordinate finite case. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {b : ℕ}

theorem unary_field_volume_integral_label_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) (τ : Fin b → Fin U.arity)
    (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hRc : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (Set.univ \ R)) :
    unaryFieldVolumeIntegral hc C Ξ FBase U =
      unaryFieldVolumeIntegral hc C Ξ FBase (U.onRVLabels hc C Ξ τ R hR hNames) +
      unaryFieldVolumeIntegral hc C Ξ FBase (U.onRVLabels hc C Ξ τ (Set.univ \ R) hRc hNames) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := U.onRVLabels hc C Ξ τ R hR hNames
  let B := U.onRVLabels hc C Ξ τ (Set.univ \ R) hRc hNames
  let W := nativeMixedVolumeDomain hc U.densityGraph.domain
  let WA := nativeMixedVolumeDomain hc A.densityGraph.domain
  let WB := nativeMixedVolumeDomain hc B.densityGraph.domain
  let T := unaryFieldVolumeContraction hc C Ξ FBase U
  have hW : GammaSetDefinable G (carrier W) := (gammaLogicInput G).real_set _ (setDefinable W)
  have hT := gamma_program_over_real_base G T.program
  obtain ⟨DA⟩ := standard_label_cut_presentation_on_equal_source T hW hT (Fin.castAdd 1 ∘ τ)
    R hR hNames WA (vf_volume_object_label_cut_density_graph hc C Ξ U τ R hR hNames).symm
  obtain ⟨DB⟩ := standard_label_cut_presentation_on_equal_source T hW hT (Fin.castAdd 1 ∘ τ)
    (Set.univ \ R) hRc hNames WB (vf_volume_object_label_cut_density_graph hc C Ξ U τ (Set.univ \ R) hRc hNames).symm
  obtain ⟨e⟩ := selected_standard_binary_restriction_volume_partition hc C Ξ W WA WB hW
    (Fin.elim0 : Fin 0 → Fin (U.arity+1)) (Fin.last U.arity)
    (unary_density_graph_label_nonzero U) (unary_density_graph_label_nonzero A) (unary_density_graph_label_nonzero B)
    (fun x _ => (U.densityGraph.finite_labels x).subset (fun _ h => h.1))
    (fun x _ => (A.densityGraph.finite_labels x).subset (fun _ h => h.1))
    (fun x _ => (B.densityGraph.finite_labels x).subset (fun _ h => h.1))
    (Fin.castAdd 1 ∘ τ) R hR hRc hNames T hT DA DB
  have hU := positiveVolumeBlowupClass_iso hc C (unaryRawSelectedVolumeIso hc C Ξ W U.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero U) T)
  have hA := positiveVolumeBlowupClass_iso hc C (unaryRawSelectedVolumeIso hc C Ξ WA A.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero A) DA.contraction)
  have hB := positiveVolumeBlowupClass_iso hc C (unaryRawSelectedVolumeIso hc C Ξ WB B.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero B) DB.contraction)
  have hIA := unary_field_volume_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 A DA.contraction
  have hIB := unary_field_volume_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 B DB.contraction
  exact hU.symm.trans ((positiveVolumeBlowupClass_iso hc C e).symm.trans
    (congrArg₂ (fun x y => x+y) (hA.trans hIA.symm) (hB.trans hIB.symm)))
end IntegrationInACVF.Section7
