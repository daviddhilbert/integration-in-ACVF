module

public import Integration7.SelectedRVVFTailProgramHeads

@[expose] public section

/-! Projection from the program-shaped VF realization retains all
original RV labels. In the final RV-only source, equal labels determine
the entire RV class of the added VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def nativeProgramSelectedRVVFTailProjection (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) :
    Map (nativeProgramSelectedRVVFTailLift hc A ρ) A :=
  Map.comp (nativeSelectedRVVFTailProjection hc A ρ)
    (nativeVFArityBackMap (Nat.add_comm n d) (nativeSelectedRVVFTailLift hc A ρ))

theorem native_program_selected_rv_vf_tail_projection_value
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) (p : nativeProgramSelectedRVVFTailLift hc A ρ) :
    (nativeProgramSelectedRVVFTailProjection hc A ρ p).val =
      ((p.val.1 ∘ finCongr (Nat.add_comm n d)) ∘ Fin.castAdd d,p.val.2) := by
  change (nativeSelectedRVVFTailProjection hc A ρ
    (nativeVFArityBackMap (Nat.add_comm n d) (nativeSelectedRVVFTailLift hc A ρ) p)).val = _
  rw [native_selected_rv_vf_tail_projection_value,native_vf_arity_back_map_value]

theorem native_program_selected_rv_vf_tail_projection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) :
    Function.Surjective (nativeProgramSelectedRVVFTailProjection hc A ρ) :=
  (native_selected_rv_vf_tail_projection_surjective hc A ρ).comp
    (native_vf_arity_back_map_bijective (Nat.add_comm n d) (nativeSelectedRVVFTailLift hc A ρ)).2

theorem native_program_selected_zero_tail_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) (p : Point (M := M) d a) :
    p ∈ carrier (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc A ρ) ↔
      (Fin.elim0,p.2) ∈ carrier A ∧ SpecialTransformations.Section4.tupleRV p.1 = p.2 ∘ ρ := by
  change p ∈ carrier (nativeVFArityCast (Nat.add_comm 0 d) (nativeSelectedRVVFTailLift hc A ρ)) ↔ _
  rw [native_vf_arity_cast_carrier,native_selected_rv_vf_tail_lift_carrier]
  have hEmpty : (p.1 ∘ finCongr (Nat.add_comm 0 d)) ∘ Fin.castAdd d = Fin.elim0 :=
    funext (fun j => j.elim0)
  have hVF : (p.1 ∘ finCongr (Nat.add_comm 0 d)) ∘ Fin.natAdd 0 = p.1 := by
    funext j
    have he : finCongr (Nat.add_comm 0 d) (Fin.natAdd 0 j) = j :=
      Fin.ext (by simp only [finCongr_apply_coe,Fin.val_natAdd,Nat.zero_add])
    exact congrArg p.1 he
  rw [hEmpty,hVF]

theorem native_program_selected_zero_tail_same_rv
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a)
    (p q : nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc A ρ)
    (hLabels : p.val.2 = q.val.2) : SameRV p.val q.val := by
  have hP := (native_program_selected_zero_tail_carrier hc A ρ p.val).mp p.property
  have hQ := (native_program_selected_zero_tail_carrier hc A ρ q.val).mp q.property
  apply (sameRV_iff _ _).mpr
  exact ⟨fun j => (congrFun hP.2 j).trans ((congrFun hLabels (ρ j)).trans (congrFun hQ.2 j).symm),hLabels⟩

end IntegrationInACVF.Section7
