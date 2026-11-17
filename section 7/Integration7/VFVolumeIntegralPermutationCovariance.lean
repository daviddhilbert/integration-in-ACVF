module

public import Integration7.NativeVFIntegralPermutationCovariance
public import Integration7.NativeVFPermutationVolumeCharts
public import Integration7.GeneratedBaseStandardContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! VF coordinate covariance of the actual positive integration
equivalence for arbitrary volume forms. A density graph supplies a literal
RV coordinate; all auxiliary graph changes preserve every VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem positive_vf_volume_integral_permutation_covariance
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (positiveVFVolumeIsoClass hc C (U.permuteVF σ)) =
      positiveVolumeClassPermute hc C σ
        (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (positiveVFVolumeIsoClass hc C U)) := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨T,_,_,_,_⟩ := generated_base_standard_contraction_exists (B := B)
    C.saturated C.model00 C.small hGenerated (Set.Subset.refl _) A hA σ
  let E := positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (k := k)
  have hGraph := congrArg E ((positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection (volumeDensityGraphBijection hc C U)⟩)
  have hPermGraph := congrArg E ((positiveVFVolumeIsoClass_eq_iff hc C).mpr
    ⟨VFVolumeIso.of_bijection ((permutedVFDensityGraphBijection hc C U σ).trans hc C
      (nativePermutedVFVolumeBijection hc C U.densityGraph σ))⟩)
  have hCov := native_vf_integral_permutation_covariance hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    A U.densityGraph.finite_labels σ U.densityGraph.form (nativePermutedVFVolumeObject hc U.densityGraph σ).form
    (Fin.last U.arity) (densityGraph_form_last U)
    (native_permuted_vf_coordinate_density hc U.densityGraph σ (Fin.last U.arity) (densityGraph_form_last U)) T
  exact hPermGraph.trans (hCov.trans (congrArg (positiveVolumeClassPermute hc C σ) hGraph.symm))

end IntegrationInACVF.Section7
