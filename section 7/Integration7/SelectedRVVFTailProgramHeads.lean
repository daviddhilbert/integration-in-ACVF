module

public import Integration7.NativeVFArityComposition
public import Integration7.SelectedRVVFTailHeadGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Lifted heads in the exact d+n arity of partial contraction
programs. The contracted target is the specified selected tail lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def nativeProgramSelectedRVVFTailLift (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S n a) (ρ : Fin d → Fin a) : DefSet (M := M) S (d+n) a :=
  nativeVFArityCast (Nat.add_comm n d) (nativeSelectedRVVFTailLift hc A ρ)

theorem native_program_selected_head_cast
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (n+1) a) (ρ : Fin d → Fin a) :
    nativeProgramSelectedRVVFTailLift hc A ρ =
      nativeVFArityCast (congrArg Nat.succ (Nat.add_comm n d)) (nativeHeadSelectedRVVFTailLift hc A ρ) := by
  change nativeVFArityCast _ _ = nativeVFArityCast _ (nativeVFArityCast _ _)
  rw [native_vf_arity_cast_trans]

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section5.HeadPreparation
open IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def selectedVFProgramTail (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a) :
    HeadPreparation (nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc A ρ) where
  arity := T.arity
  target := nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc T.target (T.selectedTailIndex ρ)
  map := nativeVFArityCastMap (Nat.add_comm (n+1) d)
    (nativeSelectedRVVFTailMap hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ))
  special := by
    have H := native_vf_arity_cast_special_relative (Nat.add_comm (n+1) d)
      (nativeSelectedRVVFTailMap hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ))
      (Fin.castAdd d (0 : Fin (n+1)))
      (native_selected_rv_vf_tail_map_special_relative hc T.map ρ (T.selectedTailIndex ρ)
        (T.selected_tail_labels ρ) 0 T.special)
    have hzero : finCongr (Nat.add_comm (n+1) d) (Fin.castAdd d (0 : Fin (n+1))) =
        (0 : Fin ((d+n)+1)) := Fin.ext rfl
    simpa only [hzero] using H
  saturated := by
    apply (headSaturated_iff_coordinateFibre _).mpr
    intro u
    change IsRVPullback (carrier (coordinateFibre
      (nativeVFArityCast (Nat.add_comm (n+1) d) (nativeSelectedRVVFTailLift hc T.target (T.selectedTailIndex ρ))) 0 u))
    rw [native_vf_arity_cast_coordinate_fibre]
    have hzero : finCongr (Nat.add_comm (n+1) d).symm (0 : Fin ((d+n)+1)) =
        Fin.castAdd d (0 : Fin (n+1)) := Fin.ext rfl
    rw [hzero]
    exact selected_vf_tail_coordinate_fibres_pullback hc T.target (T.selectedTailIndex ρ) 0
      ((headSaturated_iff_coordinateFibre T.target).mp T.saturated) _

theorem selected_vf_program_tail_contracted_set
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a) :
    (T.selectedVFProgramTail hc ρ).contractedSet =
      nativeProgramSelectedRVVFTailLift hc T.contractedSet (Fin.natAdd 1 ∘ T.selectedTailIndex ρ) := by
  change headImage (nativeProgramSelectedRVVFTailLift (n := n+1) (d := d) hc T.target (T.selectedTailIndex ρ)) = _
  rw [native_program_selected_head_cast,native_vf_arity_cast_head_image]
  have he := defSet_eq_of_carrier_eq (head_image_selected_rv_vf_tail_lift hc T.target (T.selectedTailIndex ρ))
  rw [he]
  rfl

end IntegrationInACVF.Section5.HeadPreparation
