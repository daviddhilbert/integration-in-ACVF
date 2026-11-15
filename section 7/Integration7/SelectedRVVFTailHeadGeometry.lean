import Integration7.SelectedRVVFTailHeadPreparations
import Integration7.HeadImageCoordinateWitnesses

/-! Taking a head image commutes with realization of selected RV
labels by a VF tail. The old selector shifts past the new RV head tag. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

theorem selected_vf_tail_cons_prefix (v : VF (M := M)) (x : Fin (n+d) → VF (M := M)) :
    ((Fin.cons v x) ∘ finCongr (Nat.succ_add n d)) ∘ Fin.castAdd d =
      Fin.cons v (x ∘ Fin.castAdd d) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    have he : finCongr (Nat.succ_add n d) (Fin.castAdd d j.succ) =
        (Fin.castAdd d j).succ := Fin.ext rfl
    change (Fin.cons v x : Fin ((n+d)+1) → VF (M := M)) (finCongr (Nat.succ_add n d) (Fin.castAdd d j.succ)) = _
    rw [he,Fin.cons_succ,Fin.cons_succ]
    rfl

theorem selected_vf_tail_cons_tail (v : VF (M := M)) (x : Fin (n+d) → VF (M := M)) :
    ((Fin.cons v x) ∘ finCongr (Nat.succ_add n d)) ∘ Fin.natAdd (n+1) = x ∘ Fin.natAdd n := by
  funext j
  have he : finCongr (Nat.succ_add n d) (Fin.natAdd (n+1) j) =
      (Fin.natAdd n j).succ := Fin.ext (by simp only [finCongr_apply_coe,Fin.val_natAdd,Fin.val_succ]; omega)
  change (Fin.cons v x : Fin ((n+d)+1) → VF (M := M)) (finCongr (Nat.succ_add n d) (Fin.natAdd (n+1) j)) = _
  rw [he,Fin.cons_succ]
  rfl

theorem native_head_selected_rv_vf_tail_cons
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (n+1) a) (ρ : Fin d → Fin a)
    (v : VF (M := M)) (x : Fin (n+d) → VF (M := M)) (r : Fin a → RV (M := M)) :
    (Fin.cons v x,r) ∈ carrier (nativeHeadSelectedRVVFTailLift hc A ρ) ↔
      (Fin.cons v (x ∘ Fin.castAdd d),r) ∈ carrier A ∧
        SpecialTransformations.Section4.tupleRV (x ∘ Fin.natAdd n) = r ∘ ρ := by
  change (Fin.cons v x,r) ∈ carrier
    (nativeVFArityCast (Nat.succ_add n d) (nativeSelectedRVVFTailLift hc A ρ)) ↔ _
  rw [native_vf_arity_cast_carrier,native_selected_rv_vf_tail_lift_carrier,
    selected_vf_tail_cons_prefix,selected_vf_tail_cons_tail]

theorem head_image_selected_rv_vf_tail_lift
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (n+1) a) (ρ : Fin d → Fin a) :
    carrier (headImage (nativeHeadSelectedRVVFTailLift hc A ρ)) =
      carrier (nativeSelectedRVVFTailLift hc (headImage A) (Fin.natAdd 1 ∘ ρ)) := by
  ext p
  rw [mem_head_image_coordinate_witness,native_selected_rv_vf_tail_lift_carrier,
    mem_head_image_coordinate_witness]
  constructor
  · rintro ⟨v,hv,hHead⟩
    have h := (native_head_selected_rv_vf_tail_cons hc A ρ v p.1 (p.2 ∘ Fin.natAdd 1)).mp hv
    exact ⟨⟨v,h.1,hHead⟩,h.2⟩
  · rintro ⟨⟨v,hv,hHead⟩,hTail⟩
    exact ⟨v,(native_head_selected_rv_vf_tail_cons hc A ρ v p.1 (p.2 ∘ Fin.natAdd 1)).mpr
      ⟨hv,hTail⟩,hHead⟩

end IntegrationInACVF.Section7
