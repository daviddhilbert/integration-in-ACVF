module

public import Integration7.SelectedStandardVolumeObjects
public import Integration7.FiniteContractionNormalizationVolumeIso

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual positive volume objects on the complete unnormalized labels
of an arbitrary finite-label standard contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem raw_standard_retained_density_nonzero
    {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (u : rvObjectDomain T.contractionObject) :
    (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero :=
  standard_retained_density_nonzero T δ hδ
    ⟨(Fin.elim0,u.val),(rawContractionDomain_iff T (Fin.elim0,u.val)).mp u.property⟩

def rawStandardVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) n :=
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let hA := (gammaLogicInput G).real_set _ (setDefinable A)
  let hT := gamma_program_over_real_base G T.program
  let F := FiniteRV.gammaRawFiniteContraction C.uncountable.le C.saturated C.small
    (Set.Subset.refl _) hA hfin T hT
  gammaCoordinateDensityObject (e := n) (k := 0) hc C F (Set.Subset.refl _)
    (suffixIndex T.program.rvArity_le δ) (raw_standard_retained_density_nonzero T δ hδ)

theorem raw_standard_volume_object_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    VolumeObjectGamma (rawStandardVolumeObject hc C Ξ A hfin δ hδ T)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) := by
  apply VolumeObjectGamma.of_term_context hc C
  change (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M)
  rw [Substructure.closure_eq]

end IntegrationInACVF.Section7
