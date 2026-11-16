module

public import Integration7.UnaryRawFiniteVolumeComparison
public import Integration7.RawStandardVolumeObjects
public import Integration7.CommonContextVolumeDescent
public import IntegrationSection5.NaturalContractionGamma

@[expose] public section

/-! Actual unary volume integration over a VF field base. The raw
contraction value is independent of the contraction, by the checked
unary comparison and descent to the original real parameter context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def unaryFieldVolumeContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) :
    StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) (Equiv.refl _) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  exact Classical.choose (standard_contraction_exists_with_natural_graph C.saturated C.model00 B C.small
    FBase (Set.Subset.refl _) A ((gammaLogicInput B).real_set _ (setDefinable A)) (Equiv.refl _))

theorem unary_density_graph_label_nonzero
    (U : PositiveVFVolumeObject (M := M) S 0) :
    ∀ p ∈ U.densityGraph.domain.carrier, (p.2 (Fin.last U.arity)).val ≠ iRVZero := by
  intro p hp
  apply (rv_nonzero_iff_raw _).mp
  intro h
  exact U.densityGraph.form.nonzero ⟨p,hp⟩ ((densityGraph_form_last U ⟨p,hp⟩).trans h)

theorem unary_raw_volume_contraction_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) 0)
    (T E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) (Equiv.refl _)) :
    VolumeBlowupEquivalent
      (rawStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc U.densityGraph.domain)
        U.densityGraph.finite_labels (Fin.last U.arity) (unary_density_graph_label_nonzero U) T)
      (rawStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc U.densityGraph.domain)
        U.densityGraph.finite_labels (Fin.last U.arity) (unary_density_graph_label_nonzero U) E) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let hA := (gammaLogicInput B).real_set _ (setDefinable A)
  let hT := gamma_program_over_real_base B T.program
  let hE := gamma_program_over_real_base B E.program
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc A) (Fin.last U.arity)
    (fun p => unary_density_graph_label_nonzero U p.val p.property)
  let W : PositiveVFVolumeObject (M := M) (C.base : Set M) 0 := {
    arity := U.arity+1
    domain := rawSpecialSet hc A
    finite_labels := U.densityGraph.finite_labels
    form := ω }
  have hm : PreservesVFVolume ω ω (rawSpecialMap hc (SpecialTransformations.Section5.Map.id A)) :=
    (VFVolumeBijection.refl hc C W).preserves
  obtain ⟨hδ,hε,D,hCD,h⟩ := gamma_unary_raw_finite_volume_comparison hc C C (Set.Subset.refl _)
    C.uncountable.le C.saturated C.small hΞ (Set.Subset.refl _) γ hγ hγ1
    A A hA hA U.densityGraph.finite_labels U.densityGraph.finite_labels
    (SpecialTransformations.Section5.Map.id A) Function.bijective_id
    ((gammaLogicInput B).real_map_graph _) ω ω (Fin.last U.arity) (Fin.last U.arity)
    (fun _ => rfl) (fun _ => rfl) hm T E hT hE
  let P := rawStandardVolumeObject hc C Ξ A U.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero U) T
  let Q := rawStandardVolumeObject hc C Ξ A U.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero U) E
  have H : CommonContextVolumeEquivalent B C
      ⟨P,raw_standard_volume_object_gamma hc C Ξ A _ _ _ T⟩
      ⟨Q,raw_standard_volume_object_gamma hc C Ξ A _ _ _ E⟩ := ⟨D,hCD,h⟩
  exact (H.descend hc C hNames).toOrdinary hc C B

def unaryFieldVolumeIntegral
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (FBase : VFFieldBase (C.base : Set M))
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) 0) : PositiveVolumeBlowupClasses hc C 0 :=
  positiveVolumeBlowupClass hc C (rawStandardVolumeObject hc C Ξ
    (nativeMixedVolumeDomain hc U.densityGraph.domain) U.densityGraph.finite_labels
    (Fin.last U.arity) (unary_density_graph_label_nonzero U) (unaryFieldVolumeContraction hc C Ξ FBase U))

theorem unary_field_volume_integral_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) 0)
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) (Equiv.refl _)) :
    unaryFieldVolumeIntegral hc C Ξ FBase U = positiveVolumeBlowupClass hc C
      (rawStandardVolumeObject hc C Ξ (nativeMixedVolumeDomain hc U.densityGraph.domain)
        U.densityGraph.finite_labels (Fin.last U.arity) (unary_density_graph_label_nonzero U) T) :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (unary_raw_volume_contraction_independent hc C Ξ hΞ hNames γ hγ hγ1 U _ T)

end IntegrationInACVF.Section7
