import Integration7.AERVVolumeHeadIntegrals
import Integration7.AppendedVolumeFunctionIntegrals
import Integration7.NativeAppendedVolumeIntegralFormula
import Integration7.AppendedHeadIntegralPrograms

/-! Successive integration of one VF head and the remaining VF base
equals total integration in the coefficient-first appended convention.
The proof concatenates actual contraction programs and retains the
original, possibly nonconstant density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_family_appended_integral_contraction_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k)
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) (Equiv.refl _)) :
    selectedFamilyIntegralValue hc C Ξ hGenerated F = positiveVolumeBlowupClass hc C (F.standardAppendObject hc Ξ T) :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F F
      (fun x => VolumeBlowupEquivalent.refl hc (vfParameterVolumeContext C x) _)
      (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)) T)

theorem selected_family_appended_head_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C ((n+1)+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) :
    selectedFamilyIntegralValue hc C Ξ hGenerated (F.headIntegral hc Ξ T) =
      selectedFamilyIntegralValue hc C Ξ hGenerated F := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hA : GammaSetDefinable B (carrier T.contractedSet) := (gammaLogicInput B).real_set _ (setDefinable T.contractedSet)
  obtain ⟨D,hD⟩ := generated_base_standard_contraction_exists (B := B) C.saturated C.model00 C.small
    hGenerated (Set.Subset.refl _) T.contractedSet hA (Equiv.refl _)
  let P := identityHeadTailStandardContraction T D
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))
  have hHead := native_coordinate_family_appended_integral_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    T.contractedSet (headAppendVolumeIndex T F.densityGraph.selected) (F.headIntegral hc Ξ T).finite_selected
    δ (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero) D
  have hIso := positiveVolumeBlowupClass_iso hc C
    (appendedHeadIntegralVolumeIso hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) T
      F.densityGraph.selected (Fin.last a) F.densityGraph_label_nonzero F.densityGraph.finite_selected
      (F.headIntegral hc Ξ T).finite_selected D)
  have hTotal := selected_family_appended_integral_contraction_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F P
  exact hHead.trans (hIso.trans hTotal.symm)

theorem ae_rv_volume_function_appended_head_fubini
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (f : AERVVolumeFunction hc C (n+1) k) :
    aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (aeRVVolumeFunctionHeadIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) =
      aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := by
  induction f using Quotient.inductionOn with
  | h F =>
    exact selected_family_appended_head_fubini hc C Ξ hΞ hGenerated hNames γ hγ hγ1 F.2
      (selectedFamilyHeadPreparation hc Ξ hGenerated F.2)

end IntegrationInACVF.Section7
