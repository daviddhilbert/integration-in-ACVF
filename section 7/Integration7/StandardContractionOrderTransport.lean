module

public import Integration7.SelectedStandardVolumeObjects
public import IntegrationSection6.HeadTailPermutations

@[expose] public section

/-! Changing only the proof of a contraction order keeps its final
domain, restored volume tuple and retained density unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

def standardChangeOrder {A : DefSet (M := M) S n a} {σ υ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (h : σ=υ) : StandardContraction A υ :=
  ⟨T.arity,T.target,orderedCastSource T.program (congrArg (vfPermutationImage A) h)⟩

theorem standard_change_order_volume_index {A : DefSet (M := M) S n a} {σ υ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) (h : σ=υ) : (standardChangeOrder T h).volumeIndex = T.volumeIndex := by
  cases h
  rfl

theorem head_tail_identity_order (σ : Equiv.Perm (Fin (n+1))) :
    (headTailPerm (Equiv.refl (Fin n))).trans σ = σ := by
  apply Equiv.ext
  intro j
  cases j using Fin.cases <;> rfl

theorem selected_standard_volume_object_change_order {d : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ υ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (h : σ=υ) :
    selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin (standardChangeOrder T h) =
      selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T := by
  cases h
  rfl

end IntegrationInACVF.Section7
