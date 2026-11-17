module

public import Integration7.SelectedRVVFTailProgramHeads

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal membership and finite RV fibres for the program-arity lift. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

theorem native_program_selected_rv_vf_tail_carrier
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n a)
    (ρ : Fin d → Fin a) (p : Point (M := M) (d+n) a) :
    p ∈ carrier (nativeProgramSelectedRVVFTailLift hc A ρ) ↔
      (p.1 ∘ finCongr (Nat.add_comm n d) ∘ Fin.castAdd d,p.2) ∈ carrier A ∧
      SpecialTransformations.Section4.tupleRV (p.1 ∘ finCongr (Nat.add_comm n d) ∘ Fin.natAdd n) = p.2 ∘ ρ := by
  rw [nativeProgramSelectedRVVFTailLift,native_vf_arity_cast_carrier,
    native_selected_rv_vf_tail_lift_carrier]
  rfl

theorem native_program_selected_rv_vf_tail_finite_labels
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n a)
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin d → RV (M := M)),
      {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite) (x : Fin (d+n) → VF (M := M)) :
    {r | (x,r) ∈ carrier (nativeProgramSelectedRVVFTailLift hc A ρ)}.Finite := by
  apply (hfin (x ∘ finCongr (Nat.add_comm n d) ∘ Fin.castAdd d)
    (SpecialTransformations.Section4.tupleRV (x ∘ finCongr (Nat.add_comm n d) ∘ Fin.natAdd n))).subset
  intro r hr
  have h := (native_program_selected_rv_vf_tail_carrier hc A ρ (x,r)).mp hr
  exact ⟨h.1,h.2.symm⟩

theorem native_program_selected_rv_vf_tail_density_nonzero
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n a)
    (ρ : Fin d → Fin a) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    (p : nativeProgramSelectedRVVFTailLift hc A ρ) : (p.val.2 δ).val ≠ iRVZero :=
  hδ ⟨_,((native_program_selected_rv_vf_tail_carrier hc A ρ p.val).mp p.property).1⟩

end IntegrationInACVF.Section7
