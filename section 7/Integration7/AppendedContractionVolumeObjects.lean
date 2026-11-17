module

public import Integration7.OrderedAppendVolumeFiniteness
public import Integration7.PositiveSelectedLemma75
public import Integration7.GammaTermContextVolumeGeometry
public import Integration7.RVCoordinateSelection

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual volume objects on the complete RV labels of chosen standard
contractions. Their volume tuple is the old selected coordinates followed
by all contracted VF tags; the retained old label is their density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier setDefinable gammaLogicInput)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a k : ℕ}

def standardAppendVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (appendVolumeDegree n k) where
  underlying := {
    obj := ⟨T.arity,rawVolumeContractionLabels hc T.target,
      (rvCoordinateSelectMap (C.base : Set M) (orderedAppendVolumeIndex T.program ρ)).restrict (Set.subset_univ _)⟩
    property := by
      intro y
      have hT := gamma_program_over_real_base (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.program
      have h := ordered_append_volume_fibres_finite C.uncountable.le C.saturated C.small T.program hT ρ
        (vfPermutation_selected_finite U σ ρ hfin) y.val
      apply h.of_injOn (f := fun u : rawVolumeContractionLabels hc T.target => u.val)
      · intro u hu
        exact ⟨(mem_rawVolumeContractionLabels hc T.target u.val).mp u.property,congrArg Subtype.val hu⟩
      · intro u hu v hv he
        exact Subtype.ext he }
  form := {
    map := (rvCoordinateSelectMap (C.base : Set M) (fun _ : Fin 1 => orderedAppendDensityIndex T.program δ)).restrict
      (Set.subset_univ _)
    nonzero := by
      intro u
      exact (rv_nonzero_iff_raw _).mpr
        (ordered_append_retained_density_nonzero T.program δ
          (vf_permuted_retained_density_nonzero U σ δ hδ)
          (Fin.elim0,u.val) ((mem_rawVolumeContractionLabels hc T.target u.val).mp u.property)) }

theorem standard_append_volume_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) :
    VolumeObjectGamma (standardAppendVolumeObject hc C Ξ U ρ δ hδ hfin T) ⟨(C.base : Set M),Ξ⟩ := by
  apply VolumeObjectGamma.of_term_context hc C
  change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
  rw [Substructure.closure_eq]

set_option maxHeartbeats 1600000 in
theorem standard_append_volume_object_schema_row
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction U σ) :
    let hT := gamma_program_over_real_base (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.program
    RVVolumeSchemaRow (standardAppendVolumeObject hc C Ξ U ρ δ hδ hfin T)
      (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
        (orderedAppendVolumeIndex T.program ρ) (orderedAppendDensityIndex T.program δ))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  intro hT
  have hTarget := gamma_program_final_set T.program hT
  have hNZ := ordered_append_retained_density_nonzero T.program δ
    (vf_permuted_retained_density_nonzero U σ δ hδ)
  constructor
  · intro r y
    have h := gammaSelectedLabelSchema_volume T.target hTarget (orderedAppendVolumeIndex T.program ρ)
      (Fin.elim0 : Fin 0 → VF (M := M)) r y
    constructor
    · intro hr
      obtain ⟨hmem,hv⟩ := h.mp hr
      exact ⟨⟨r,(mem_rawVolumeContractionLabels hc T.target r).mpr hmem⟩,rfl,hv⟩
    · rintro ⟨u,hu,hv⟩
      apply h.mpr
      exact ⟨hu ▸ (mem_rawVolumeContractionLabels hc T.target u.val).mp u.property,
        (congrArg (fun r => r ∘ orderedAppendVolumeIndex T.program ρ) hu).symm.trans hv⟩
  · intro r w
    have h := gammaSelectedVolumeSchema_density T.target hTarget (orderedAppendVolumeIndex T.program ρ)
      (orderedAppendDensityIndex T.program δ) hNZ (Fin.elim0 : Fin 0 → VF (M := M)) r w
    constructor
    · intro hr
      obtain ⟨hmem,hw⟩ := h.mp hr
      exact ⟨⟨r,(mem_rawVolumeContractionLabels hc T.target r).mpr hmem⟩,rfl,hw⟩
    · rintro ⟨u,hu,hw⟩
      apply h.mpr
      refine ⟨hu ▸ (mem_rawVolumeContractionLabels hc T.target u.val).mp u.property,?_⟩
      change (fun _ : Fin 1 => r (orderedAppendDensityIndex T.program δ)) = w
      change (fun _ : Fin 1 => u.val (orderedAppendDensityIndex T.program δ)) = w at hw
      rw [hu] at hw
      exact hw

end IntegrationInACVF.Section7
