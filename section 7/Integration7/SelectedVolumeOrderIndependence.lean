module

public import Integration7.SelectedSameOrderStandardVolumeComparison
public import Integration7.SelectedFirstTwoStandardVolumeExchange

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The all-order comparison property on actual selected-volume objects.
Only positive VF arities are needed; a contracted first head supplies
the positive retained RV degree in the induction. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def SelectedVolumeOrderIndependent (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) (n : ℕ) : Prop :=
  ∀ {a d : ℕ} (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin (n+1))) (T : StandardContraction A σ) (E : StandardContraction A υ),
    CommonContextVolumeEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) C
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin T⟩
      ⟨selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin E,
        selected_standard_volume_object_gamma hc C Ξ A ρ δ hδ hfin E⟩

end IntegrationInACVF.Section7
