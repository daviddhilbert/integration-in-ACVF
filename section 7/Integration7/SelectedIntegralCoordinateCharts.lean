module

public import Integration7.SelectedIntegralCoordinateOrder
public import Integration7.VolumeBlowupCoordinatePermutations
public import Integration7.VolumeBlowupRightProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal RV charts compare the appended and original-coordinate
presentations of the same selected integral. The common permutation and
unchanged retained density are explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

theorem selected_append_degree_eq (n k : ℕ) : appendVolumeDegree (n+1) k = (k+1)+n := by
  rw [append_volume_degree_eq]
  omega

theorem selected_integral_coordinate_chart_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _))
    (u : (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).underlying.obj.domain) :
    ((selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).reindexDegree (selected_append_degree_eq n k)).underlying.obj.value u =
      (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).underlying.obj.value u ∘
        appendedToOriginalVolumePermutation (n+1) k := by
  funext i
  change u.val (selectedStandardVolumeIndex T ρ (finCongr (append_volume_length_eq (n+1) k) i)) = _
  exact congrArg u.val (congrFun (identity_selected_volume_index_from_append T ρ) i)

def selectedIntegralCoordinateChart
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) :
    (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).underlying ≅
      ((selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).reindexDegree (selected_append_degree_eq n k)).underlying :=
  rvFiniteIsoOfAmbient (rvIsoOfLabelEquiv (Map.id _) Function.bijective_id
    (rvReindexEquiv (appendedToOriginalVolumePermutation (n+1) k))
    (rvWeight_reindex (appendedToOriginalVolumePermutation (n+1) k))
    (selected_integral_coordinate_chart_coordinates hc C Ξ A ρ δ hδ hfin T))

theorem selected_integral_coordinate_chart_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _))
    (u : (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).underlying.obj.domain) :
    ((selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).reindexDegree (selected_append_degree_eq n k)).form.value
        (finiteIsoMap (selectedIntegralCoordinateChart hc C Ξ A ρ δ hδ hfin T) u) =
      (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).form.value u := by
  change u.val (suffixIndex T.program.rvArity_le δ) = u.val (orderedAppendDensityIndex T.program δ)
  rw [ordered_append_density_index]

theorem VolumeBlowupEquivalent.of_reindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {p q : ℕ} (h : p=q)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) q}
    (hUV : VolumeBlowupEquivalent (U.reindexDegree h) (V.reindexDegree h)) : VolumeBlowupEquivalent U V := by
  cases h
  exact ((VolumeBlowupEquivalent.of_iso C ((volumeCastReindexIso hc C U rfl).symm hc C)).trans hc C hUV).trans hc C
    (VolumeBlowupEquivalent.of_iso C (volumeCastReindexIso hc C V rfl))

end IntegrationInACVF.Section7
