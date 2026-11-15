import Integration7.PermutedDensityGraphFamilyIntegrals
import Integration7.CanonicalVolumeIntegralContractionFormula
import Integration7.PermutedNativeContractionVolumeCharts
import Integration7.AERVVolumePermutedFunctions

/-! The canonical family integral is covariant under VF coordinate
reindexing: exactly the corresponding VF block of its RV coordinates is
reindexed, and the density remains unchanged. Inverse reindexing restores
the original ordered integral on the actual almost-everywhere quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_family_canonical_integral_permute_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C (n+1) a k) (σ : Equiv.Perm (Fin (n+1))) :
    selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated (F.permuteBase σ) =
      positiveVolumeClassPermute (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ)
        (selectedFamilyCanonicalIntegralValue hc C Ξ hGenerated F) := by
  let T := selectedFamilyIntegralContraction hc C Ξ hGenerated F σ
  let D := identityContractionOnPermutedSource T
  let U := F.canonicalIntegralObject hc Ξ T
  have hF := selected_family_canonical_integral_standard_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F T
  have hG := permuted_density_graph_family_integral_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F σ D
  have hIso := positiveVolumeBlowupClass_iso hc C
    (permutedNativeContractionVolumeIso hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain)
      F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected T)
  have hExpected := (congrArg (positiveVolumeClassPermute (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ)) hF).trans
    (positive_volume_class_permute_representative (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ) U)
  exact hG.trans (hIso.symm.trans hExpected.symm)

theorem ae_rv_volume_function_integral_permute_base
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C n k) (σ : Equiv.Perm (Fin (n+1))) :
    aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (aeRVVolumeFunctionPermuteBase hc C σ f) =
      positiveVolumeClassPermute (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ)
        (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F => exact selected_family_canonical_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2 σ

theorem ae_rv_volume_function_integral_restore_order
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C n k) (σ : Equiv.Perm (Fin (n+1))) :
    positiveVolumeClassPermute (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ).symm
      (aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (aeRVVolumeFunctionPermuteBase hc C σ f)) =
        aeRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  rw [ae_rv_volume_function_integral_permute_base hc C Ξ hΞ hGenerated hNames γ hγ hγ1]
  exact (positiveVolumeClassPermutationEquiv (k := (k+1)+n) hc C (selectedVFTailPermutation (n := n+1) (k+1) σ)).left_inv _

end IntegrationInACVF.Section7
