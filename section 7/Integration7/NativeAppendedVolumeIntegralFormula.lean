module

public import Integration7.NativeVolumeFamilyIntegralFormula
public import Integration7.SelectedIntegralCoordinateEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Compute the coefficient-first integral of a literal density family
using a specified identity-order native contraction, without adding a
new density graph to that program. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem native_coordinate_family_appended_integral_formula
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (T : StandardContraction A (Equiv.refl _)) :
    selectedFamilyIntegralValue hc C Ξ hGenerated (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ) =
      positiveVolumeBlowupClass hc C (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T) := by
  let F := nativeCoordinateVolumeFamily hc A ρ hfin δ hδ
  let E := selectedFamilyIntegralContraction hc C Ξ hGenerated F (Equiv.refl _)
  have h := (positiveVolumeBlowupClass_eq_iff hc C).mp
    (native_coordinate_family_canonical_integral_formula hc C Ξ hΞ hGenerated hNames γ hγ hγ1 A ρ hfin δ hδ T)
  exact (positiveVolumeBlowupClass_eq_iff hc C).mpr
    (selected_appended_common_of_canonical hc C Ξ (nativeMixedVolumeDomain hc F.densityGraph.domain) A
      F.densityGraph.selected ρ (Fin.last a) δ F.densityGraph_label_nonzero hδ
      F.densityGraph.finite_selected hfin E T h)

end IntegrationInACVF.Section7
