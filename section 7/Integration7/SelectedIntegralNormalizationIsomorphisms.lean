module

public import Integration7.SelectedIntegralCoordinateCharts
public import Integration7.GammaPermutedVolumeObjects

@[expose] public section

/-! Once the appended volume tuple is explicitly reindexed, the
canonical contraction object has literally identical coordinates and
density. The identity on RV labels is then a genuine volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k : ℕ}

def selectedIntegralNormalizationIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) :
    RVVolumeIso ((standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).permuteVolume
      (appendedToOriginalVolumePermutation (n+1) k))
      ((selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).reindexDegree (selected_append_degree_eq n k)) := by
  let U := (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin T).permuteVolume
    (appendedToOriginalVolumePermutation (n+1) k)
  let V := (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).reindexDegree (selected_append_degree_eq n k)
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.id _
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u :=
    selected_integral_coordinate_chart_coordinates hc C Ξ A ρ δ hδ hfin T
  have hForm : ∀ u, V.form.value (f u) = U.form.value u := by
    intro u
    change u.val (suffixIndex T.program.rvArity_le δ) = u.val (orderedAppendDensityIndex T.program δ)
    rw [ordered_append_density_index]
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord hForm

end IntegrationInACVF.Section7
