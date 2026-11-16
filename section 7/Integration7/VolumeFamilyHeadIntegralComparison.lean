module

public import Integration7.NativeCoordinateVolumeFamilyRows
public import Integration7.GammaHeadVolumeCommonComparison
public import Integration7.SelectedFamilyGeometricCommon

@[expose] public section

/-! Genuine one-head fibre integration preserves the ordinary row
common-blowup relation. All comparisons descend to the original finite
VF parameter context of the retained tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b k : ℕ}

theorem selected_family_head_integral_comparison
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.densityGraph.domain))
    (x : Fin n → VF (M := M)) :
    VolumeBlowupEquivalent ((F.headIntegral hc Ξ T).rowInContext x)
      ((G.headIntegral hc Ξ E).rowInContext x) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := nativeMixedVolumeDomain hc F.densityGraph.domain
  let V := nativeMixedVolumeDomain hc G.densityGraph.domain
  have hU : GammaSetDefinable B (carrier U) := (gammaLogicInput B).real_set _ (setDefinable U)
  have hV : GammaSetDefinable B (carrier V) := (gammaLogicInput B).real_set _ (setDefinable V)
  have hT := (gammaLogicInput B).real_map_graph T.map
  have hE := (gammaLogicInput B).real_map_graph E.map
  have hTarget := (gammaLogicInput B).real_set _ (setDefinable T.target)
  have hETarget := (gammaLogicInput B).real_set _ (setDefinable E.target)
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))
  let ε := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) (Fin.last b))
  let L := gammaSelectedVolumeSchema T.contractedSet (gamma_headImage T.target hTarget)
    (headAppendVolumeIndex T F.densityGraph.selected) δ
  let R := gammaSelectedVolumeSchema E.contractedSet (gamma_headImage E.target hETarget)
    (headAppendVolumeIndex E G.densityGraph.selected) ε
  apply volume_family_geometric_rows_descend hc Ξ hNames
    (F.headIntegral hc Ξ T) (G.headIntegral hc Ξ E) L R x
  · exact native_coordinate_volume_family_schema_row hc T.contractedSet _ _ _ δ _ x
  · exact native_coordinate_volume_family_schema_row hc E.contractedSet _ _ _ ε _ x
  · exact gamma_head_volume_common_comparison hc C C.uncountable.le C.saturated C.model00
      C.small hΞ γ hγ hγ1 (Set.Subset.refl _) U V hU hV
      F.densityGraph.selected G.densityGraph.selected (Fin.last a) (Fin.last b)
      F.densityGraph_label_nonzero G.densityGraph_label_nonzero
      F.densityGraph.finite_selected G.densityGraph.finite_selected
      (fun y => selected_densityGraph_geometric_common hc Ξ F G y (hCommon y))
      T E hT hE hTarget hETarget x

theorem selected_family_head_integral_choice_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k)
    (T E : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (x : Fin n → VF (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ T).rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.headIntegral hc Ξ E).rowInContext x) :=
  (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mpr
    (selected_family_head_integral_comparison hc Ξ hΞ hNames γ hγ hγ1 F F
      (fun y => VolumeBlowupEquivalent.refl hc (vfParameterVolumeContext C y) _) T E x)

end IntegrationInACVF.Section7
