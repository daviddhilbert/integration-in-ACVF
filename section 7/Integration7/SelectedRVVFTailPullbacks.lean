module

public import Integration7.SelectedRVVFTailProgramHeads
public import Section5.UnaryMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Selected-label VF realizations of RV-pullbacks are RV-pullbacks.
In particular the remaining VF tail after the lifted original program
admits a canonical identity-head contraction. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a d : ℕ}

theorem native_vf_arity_cast_pullback (h : n = m) (A : DefSet (M := M) S n a)
    (hA : IsRVPullback (carrier A)) : IsRVPullback (carrier (nativeVFArityCast h A)) := by
  cases h
  exact hA

theorem native_selected_rv_vf_tail_lift_pullback
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (nativeSelectedRVVFTailLift hc A ρ)) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hP := (native_selected_rv_vf_tail_lift_carrier hc A ρ p).mp hp
  obtain ⟨hVF,hRV⟩ := (sameRV_iff p q).mp he
  have hPrefix : SameRV (p.1 ∘ Fin.castAdd d,p.2) (q.1 ∘ Fin.castAdd d,q.2) :=
    (sameRV_iff _ _).mpr ⟨fun j => hVF (Fin.castAdd d j),hRV⟩
  apply (native_selected_rv_vf_tail_lift_carrier hc A ρ q).mpr
  refine ⟨(isRVPullback_iff _).mp hA _ hP.1 _ hPrefix,?_⟩
  funext j
  change rv (q.1 (Fin.natAdd n j)) = q.2 (ρ j)
  exact (hVF (Fin.natAdd n j)).symm.trans ((congrFun hP.2 j).trans (congrFun hRV (ρ j)))

theorem native_program_selected_rv_vf_tail_lift_pullback
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) (hA : IsRVPullback (carrier A)) :
    IsRVPullback (carrier (nativeProgramSelectedRVVFTailLift hc A ρ)) :=
  native_vf_arity_cast_pullback (Nat.add_comm n d) _ (native_selected_rv_vf_tail_lift_pullback hc A ρ hA)

end IntegrationInACVF.Section7
