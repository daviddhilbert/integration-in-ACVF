module

public import Integration7.GammaRVDefinableNameContexts
public import IntegrationSection6.GammaNamedRVFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual name certificates for the original Gamma base augmented by
one finite RV tuple. No VF representatives of those RV values are added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {d : ℕ}

theorem rv_parameter_tuple_singleton (P : Base (M := M)) (u : Fin d → CanonicalRV.RVSort M) :
    DefinableOverBase (RVLabelSlices.labelBase P u) (fun _ : Fin d => .rv) {fun j => (u j).val} := by
  let B := RVLabelSlices.labelBase P u
  exact tuple_singleton_definable_base B _ _ (fun j => real_definableAtBase B .rv _
    (definableClosureAt_of_mem (Or.inr ⟨j,rfl⟩) (u j).property))

theorem rv_cell_fibre_real_names (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk P.gamma < C.κ) (u : Fin d → CanonicalRV.RVSort M) :
    (RVLabelSlices.labelBase P u).real ⊆ ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ u).base : Set M) := by
  intro y hy
  apply gamma_rv_definable_names_context_contains hc C P hPC hΓ u
  exact hy.elim (fun h => Or.inl (Or.inl (hPC h))) Or.inr

theorem rv_cell_fibre_common_names (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk P.gamma < C.κ) (u : Fin d → CanonicalRV.RVSort M) :
    commonRealNames (RVLabelSlices.labelBase P u) ⊆
      ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ u).base : Set M) := by
  rintro y (hy | hy)
  · exact rv_cell_fibre_real_names hc C P hPC hΓ u hy
  · exact gamma_rv_definable_names_context_contains hc C P hPC hΓ u (Or.inl (Or.inr (Or.inr hy)))

theorem rv_cell_fibre_tuple_names (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (P : Base (M := M)) (hPC : P.real ⊆ (C.base : Set M))
    (hΓ : Cardinal.mk P.gamma < C.κ) (u : Fin d → CanonicalRV.RVSort M) :
    ∀ j, (u j).val ∈ ((gammaRVDefinableNamesVolumeContext hc C P hPC hΓ u).base : Set M) := by
  intro j
  exact gamma_rv_definable_names_context_contains hc C P hPC hΓ u (Or.inr ⟨j,rfl⟩)

end IntegrationInACVF.Section7
