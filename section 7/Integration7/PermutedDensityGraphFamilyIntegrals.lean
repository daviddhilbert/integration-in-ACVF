import Integration7.PermutedVolumeFamilyRows
import Integration7.NativeCoordinateFamilyRowIdentifications
import Integration7.NativeVolumeFamilyIntegralFormula

/-! Reindexing a family and then appending its density represents the
same named RV fibres as reindexing its original density graph. This
computes the reindexed integral on the original permuted native graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def permutedFamilyDensityGraphRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → VF (M := M)) :
    RVVolumeIso ((F.permuteBase σ).rowInContext x) ((F.densityGraph.permuteBase σ).rowInContext x) := by
  let D := vfParameterVolumeContext C x
  let h := vf_parameter_volume_context_permutation_subset C σ x
  exact ((permutedVolumeFamilyRowIso hc F σ x).trans hc D
    ((F.densityGraphRowIso hc (x ∘ σ.symm)).extend h)).trans hc D
      ((permutedVolumeFamilyRowIso hc F.densityGraph σ x).symm hc D)

theorem permuted_density_graph_native_carrier
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (σ : Equiv.Perm (Fin n)) :
    (F.densityGraph.permuteBase σ).domain.carrier =
      carrier (vfPermutationImage (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) := by
  ext p
  change (p.1,p.2) ∈ (mixedVFPermutationDomain F.densityGraph.domain σ).carrier ↔
    (p.1,p.2) ∈ carrier (vfPermutationImage (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
  rw [mem_mixed_vf_permutation_domain,vfPermutationImage_row]
  rfl

theorem permuted_density_graph_family_integral_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (σ : Equiv.Perm (Fin (n+1)))
    {τ : Equiv.Perm (Fin (n+1))}
    (D : StandardContraction (vfPermutationImage (nativeMixedVolumeDomain hc F.densityGraph.domain) σ) τ) :
    let A := nativeMixedVolumeDomain hc F.densityGraph.domain
    let hfin := vfPermutation_selected_finite A σ F.densityGraph.selected F.densityGraph.finite_selected
    let hδ := vf_permuted_retained_density_nonzero A σ (Fin.last a) F.densityGraph_label_nonzero
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (F.permuteBase σ) =
      positiveVolumeBlowupClass hc C
        (selectedStandardVolumeObject hc C Ξ (vfPermutationImage A σ) F.densityGraph.selected (Fin.last a) hδ hfin D) := by
  intro A hfin hδ
  let B := vfPermutationImage A σ
  let N := nativeCoordinateVolumeFamily hc B F.densityGraph.selected hfin (Fin.last a) hδ
  have hDensity : ∀ q : (F.densityGraph.permuteBase σ).domain,
      (F.densityGraph.permuteBase σ).form.value q = q.val.2 (Fin.last a) := by
    intro q
    exact (F.densityGraph.permuteBase_density σ q).trans (F.densityGraph_form_last _)
  have hPoint : ∀ x, VolumeBlowupEquivalent ((F.permuteBase σ).rowInContext x) (N.rowInContext x) := by
    intro x
    let e := nativeCoordinateFamilyRowIso hc (F.densityGraph.permuteBase σ) B F.densityGraph.selected hfin
      (Fin.last a) hδ (permuted_density_graph_native_carrier hc F σ) rfl hDensity x
    exact VolumeBlowupEquivalent.of_iso (vfParameterVolumeContext C x)
      ((permutedFamilyDensityGraphRowIso hc F σ x).trans hc (vfParameterVolumeContext C x)
        (e.symm hc (vfParameterVolumeContext C x)))
  exact (selected_family_canonical_integral_value_independent hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    (F.permuteBase σ) N hPoint).trans
      (native_coordinate_family_canonical_integral_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        B F.densityGraph.selected hfin (Fin.last a) hδ D)

end IntegrationInACVF.Section7
