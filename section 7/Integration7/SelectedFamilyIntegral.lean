module

public import Integration7.SelectedFamilyIntegralComparison
public import Integration7.GeneratedBaseStandardContractions
public import Integration7.VolumeBlowupClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual positive homogeneous RV-family integral representatives.
The choice of contraction is eliminated by the proved comparison theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

def selectedFamilyIntegralContraction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C n a k) (σ : Equiv.Perm (Fin n)) :
    StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc F.densityGraph.domain
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  exact Classical.choose (generated_base_standard_contraction_exists (B := B)
    C.saturated C.model00 C.small hGenerated (Set.Subset.refl _) A hA σ)

def selectedFamilyIntegralValue
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (F : SelectedVFVolumeFamily C n a k) : PositiveVolumeBlowupClasses hc C (appendVolumeDegree n k) :=
  positiveVolumeBlowupClass hc C
    (F.standardAppendObject hc Ξ (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)))

theorem selected_family_integral_value_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x)) :
    selectedFamilyIntegralValue hc C Ξ hGenerated F = selectedFamilyIntegralValue hc C Ξ hGenerated G :=
  (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_family_integral_comparison hc C Ξ hΞ hNames γ hγ hγ1 F G hCommon
      (selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _))
      (selectedFamilyIntegralContraction hc C Ξ hGenerated G (Equiv.refl _)))

end IntegrationInACVF.Section7
