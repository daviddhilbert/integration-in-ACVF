import Integration7.VolumeFamilyFormulaWitnessDescent
import Integration7.ChosenVolumeFamilyHeadIntegrals
import Integration7.GenericHeadVolumeCommonComparison

/-! Head fibre integration respects equality outside a definable
VF-small set. Generic head comparison and a finite formula cover produce
one definable small exceptional set in the retained VF base. -/
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

theorem selected_family_ae_common_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (hAE : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (x : Fin (n+1) → VF (M := M))
    (hx : AlgebraicIndependent (vfParameterField (C.base : Set M)) x) :
    VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x) := by
  obtain ⟨E,hE,hRows⟩ := hAE
  exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mp
    (hRows x (fun h => pure_vf_small_has_no_independent hc E hE ⟨x,h⟩ hx))

theorem selected_family_head_integral_ae_comparison
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C ((n+1)+1) a k) (G : SelectedVFVolumeFamily C ((n+1)+1) b k)
    (hAE : AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.densityGraph.domain)) :
    AERVVolumeFunctionEquivalent hc C ⟨1+T.arity,F.headIntegral hc Ξ T⟩
      ⟨1+E.arity,G.headIntegral hc Ξ E⟩ := by
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
  let LF := gammaSelectedVolumeSchema T.contractedSet (gamma_headImage T.target hTarget)
    (headAppendVolumeIndex T F.densityGraph.selected) δ
  let RG := gammaSelectedVolumeSchema E.contractedSet (gamma_headImage E.target hETarget)
    (headAppendVolumeIndex E G.densityGraph.selected) ε
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound C.uncountable.le C.saturated C.small hΞ
    T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T F.densityGraph.selected) δ
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero)
    (F.headIntegral hc Ξ T).finite_selected
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound C.uncountable.le C.saturated C.small hΞ
    E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E G.densityGraph.selected) ε
    (head_retained_density_nonzero E (Fin.last b) G.densityGraph_label_nonzero)
    (G.headIntegral hc Ξ E).finite_selected
  apply volume_family_ae_of_generic_formula_witnesses hc Ξ hΞ hNames
    (F.headIntegral hc Ξ T) (G.headIntegral hc Ξ E) (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row hc T.contractedSet _ _ _ δ _ x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row hc E.contractedSet _ _ _ ε _ x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc C.uncountable.le C.saturated C.model00
      C.small hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact gamma_head_volume_common_comparison_at_generic hc C C.uncountable.le C.saturated C.model00
      C.small hΞ γ hγ hγ1 (Set.Subset.refl _) U V hU hV
      F.densityGraph.selected G.densityGraph.selected (Fin.last a) (Fin.last b)
      F.densityGraph_label_nonzero G.densityGraph_label_nonzero
      F.densityGraph.finite_selected G.densityGraph.finite_selected
      (fun y hy => selected_densityGraph_geometric_common hc Ξ F G y
        (selected_family_ae_common_at_generic hc F G hAE y hy)) T E hT hE hTarget hETarget x hx

end IntegrationInACVF.Section7
