module

public import Integration7.VFBaseDimensionBounds
public import Integration7.VFCofullSubdomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restrictions of actual RV-valued families and the cofull VF
realizations of restrictions whose discarded base domain is VF-small. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def SelectedVFVolumeFamily.restrict (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) : SelectedVFVolumeFamily C n a k where
  domain := L
  selected := F.selected
  finite_selected x t := (F.finite_selected x t).subset (fun r h => ⟨hL h.1,h.2⟩)
  form := F.form.restrict hL

theorem selected_family_full_lift_restrict_subset
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) :
    (F.restrict L hL).fullLift.domain.carrier ⊆ F.fullLift.domain.carrier := by
  intro p hp
  have h := (mem_selected_rv_vf_tail_lift L F.selected p).mp hp
  exact (mem_selected_rv_vf_tail_lift F.domain F.selected p).mpr ⟨hL h.1,h.2⟩

theorem selected_family_full_lift_restrict_cofull
    (F : SelectedVFVolumeFamily C n a k)
    (L : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier)
    (hSmall : vfDim (rawRVSpace (M := M) 1) (F.domain.sdiff L) < n) :
    VFCofull F.fullLift.domain (F.restrict L hL).fullLift.domain := by
  refine ⟨selected_family_full_lift_restrict_subset F L hL,?_⟩
  let E := selectedRVVFTailLift (n := n) (d := k+1) (F.domain.sdiff L) F.selected
  have hSub : (F.fullLift.domain.sdiff (F.restrict L hL).fullLift.domain).carrier ⊆ E.carrier := by
    intro p hp
    have h := (mem_selected_rv_vf_tail_lift F.domain F.selected p).mp hp.1
    apply (mem_selected_rv_vf_tail_lift (F.domain.sdiff L) F.selected p).mpr
    exact ⟨⟨h.1,fun hl => hp.2 ((mem_selected_rv_vf_tail_lift L F.selected p).mpr ⟨hl,h.2⟩)⟩,h.2⟩
  exact (vfDim_mono_same_arity hSub).trans_lt
    ((selected_rv_vf_tail_lift_dim_le (F.domain.sdiff L) F.selected).trans_lt (by omega))

end IntegrationInACVF.Section7
