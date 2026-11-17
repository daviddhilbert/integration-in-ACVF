module

public import Integration7.FieldBaseVolumeFamilyIntegrals
public import Integration7.SelectedVolumeFamilyLabelCuts
public import Integration7.SelectedStandardBinaryVolumePartitions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Chosen field-base integrals respect complementary old-label cuts.
One actual contraction is restricted to the two pieces, so no lift theorem
requiring a stronger generated-base hypothesis is invoked. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_family_field_canonical_integral_contraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) (Equiv.refl _)) :
    selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F =
      positiveVolumeBlowupClass hc C (F.canonicalIntegralObject hc Ξ T) :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_canonical_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F F
      (fun x => VolumeBlowupEquivalent.refl hc (vfParameterVolumeContext C x) (F.rowInContext x))
      (selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)) T)

theorem selected_family_field_integral_label_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ) (FBase : VFFieldBase (C.base : Set M))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (τ : Fin b → Fin a)
    (R : Set (Point (M := M) 0 b))
    (hR : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) R)
    (hRc : GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (Set.univ \ R)) :
    selectedFamilyFieldCanonicalIntegral hc C Ξ FBase F =
      selectedFamilyFieldCanonicalIntegral hc C Ξ FBase (F.onRVLabels hc Ξ τ R hR hNames) +
      selectedFamilyFieldCanonicalIntegral hc C Ξ FBase (F.onRVLabels hc Ξ τ (Set.univ \ R) hRc hNames) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  let A := F.onRVLabels hc Ξ τ R hR hNames
  let B := F.onRVLabels hc Ξ τ (Set.univ \ R) hRc hNames
  let UA := nativeMixedVolumeDomain hc A.densityGraph.domain
  let UB := nativeMixedVolumeDomain hc B.densityGraph.domain
  let T := selectedFamilyFieldIntegralContraction hc C Ξ FBase F (Equiv.refl _)
  have hU : GammaSetDefinable G (carrier U) := (gammaLogicInput G).real_set _ (setDefinable U)
  have hT := gamma_program_over_real_base G T.program
  obtain ⟨DA⟩ := standard_label_cut_presentation_on_equal_source T hU hT (Fin.castAdd 1 ∘ τ)
    R hR hNames UA (selected_family_label_cut_density_graph hc Ξ F τ R hR hNames).symm
  obtain ⟨DB⟩ := standard_label_cut_presentation_on_equal_source T hU hT (Fin.castAdd 1 ∘ τ)
    (Set.univ \ R) hRc hNames UB
    (selected_family_label_cut_density_graph hc Ξ F τ (Set.univ \ R) hRc hNames).symm
  obtain ⟨e⟩ := selected_standard_binary_restriction_volume_partition hc C Ξ U UA UB hU
    F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero A.densityGraph_label_nonzero
    B.densityGraph_label_nonzero F.densityGraph.finite_selected A.densityGraph.finite_selected B.densityGraph.finite_selected
    (Fin.castAdd 1 ∘ τ) R hR hRc hNames T hT DA DB
  have he := positiveVolumeBlowupClass_iso hc C e
  have hA := selected_family_field_canonical_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 A DA.contraction
  have hB := selected_family_field_canonical_integral_contraction hc C Ξ hΞ FBase hNames γ hγ hγ1 B DB.contraction
  exact he.symm.trans (congrArg₂ (fun x y => x+y) hA.symm hB.symm)
end IntegrationInACVF.Section7
