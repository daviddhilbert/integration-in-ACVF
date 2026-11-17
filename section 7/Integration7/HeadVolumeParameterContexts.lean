module

public import Integration7.HeadFibreRawVolumePresentation
public import Integration7.FiniteVolumeParameterContexts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A head fibre has a genuine small containing context naming exactly
the frozen VF tuple in addition to the previous containing context. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

def headVolumeParameterContext (C : BaseContext M) (x : Fin n → VF (M := M)) : BaseContext M :=
  finiteVolumeParameterContext C (Set.range (fun j => (x j).val)) (Set.finite_range _)

theorem head_volume_context_contains (C : BaseContext M) (x : Fin n → VF (M := M)) :
    (C.base : Set M) ∪ Set.range (fun j => (x j).val) ⊆ ((headVolumeParameterContext C x).base : Set M) :=
  finiteVolumeParameterContext_contains C _ _

theorem head_volume_context_contains_fibre_base (C : BaseContext M) (x : Fin n → VF (M := M)) :
    coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) ⊆ ((headVolumeParameterContext C x).base : Set M) := by
  rw [head_coordinate_fibre_base]
  exact head_volume_context_contains C x

theorem head_volume_context_contains_original_base (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (x : Fin n → VF (M := M)) :
    B.real ∪ Set.range (fun j => (x j).val) ⊆ ((headVolumeParameterContext C x).base : Set M) :=
  (Set.union_subset_union hBC (Set.Subset.refl _)).trans (head_volume_context_contains C x)

end IntegrationInACVF.Section7
