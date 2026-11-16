module

public import Integration7.SelectedStandardVolumeFiniteness
public import Integration7.AppendedContractionVolumeObjects
public import Integration7.OrderedAppendVolumeIndices
public import Integration7.NativeCoordinateDensityVolumeObjects

@[expose] public section

/-! Selected standard-contraction volume objects whose VF block is in
the original coordinate order, followed by the selected old RV block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

theorem standard_retained_density_nonzero
    {S : Set M} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) (q : T.target) :
    (q.val.2 (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero :=
by
  obtain ⟨p,hp⟩ := T.program.surjective q
  have hq := T.program.oldLabels p δ
  rw [hp] at hq
  change q.val.2 (suffixIndex T.program.rvArity_le δ) = p.val.2 δ at hq
  rw [hq]
  exact vf_permuted_retained_density_nonzero A σ δ hδ p.val p.property

def selectedStandardVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) (d+n) :=
  nativeCoordinateDensityVolumeObject hc C T.target (selectedStandardVolumeIndex T ρ)
    (suffixIndex T.program.rvArity_le δ) (selected_standard_volume_fibres_finite hc C Ξ A ρ hfin T)
    (standard_retained_density_nonzero T δ hδ)

theorem selected_standard_volume_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    VolumeObjectGamma (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) :=
  native_coordinate_density_volume_object_gamma hc C Ξ _ _ _ _ _

end IntegrationInACVF.Section7
