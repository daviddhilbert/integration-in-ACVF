module

public import IntegrationSection5.HeadContractionGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal membership in a head contraction image, using a witness
for the removed VF coordinate and the retained old RV labels. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem mem_head_image_coordinate_witness
    (A : DefSet (M := M) S (n+1) a) (p : Point (M := M) n (1+a)) :
    p ∈ carrier (headImage A) ↔ ∃ v : VF (M := M),
      (Fin.cons v p.1,p.2 ∘ Fin.natAdd 1) ∈ carrier A ∧
        rv v = p.2 (Fin.castAdd a (0 : Fin 1)) := by
  rw [headImage_carrier]
  constructor
  · rintro ⟨q,hq,he⟩
    have hx := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change Fin.tail q.1 = p.1 at hx
    change Fin.append (fun _ : Fin 1 => rv (q.1 0)) q.2 = p.2 at hr
    have hRV : p.2 ∘ Fin.natAdd 1 = q.2 := by
      funext j
      exact (congrFun hr (Fin.natAdd 1 j)).symm.trans (Fin.append_right _ _ j)
    have hOriginal : (Fin.cons (q.1 0) p.1,p.2 ∘ Fin.natAdd 1) = q := by
      refine Prod.ext ?_ hRV
      rw [← hx]
      exact Fin.cons_self_tail q.1
    refine ⟨q.1 0,?_,?_⟩
    · exact Eq.mp (congrArg (fun z => z ∈ carrier A) hOriginal.symm) hq
    · exact (Fin.append_left _ _ (0 : Fin 1)).symm.trans (congrFun hr (Fin.castAdd a 0))
  · rintro ⟨v,hA,hv⟩
    refine ⟨(Fin.cons v p.1,p.2 ∘ Fin.natAdd 1),hA,?_⟩
    change ((fun j : Fin n => (Fin.cons v p.1 : Fin (n+1) → VF (M := M)) j.succ),Fin.append (fun _ : Fin 1 => rv v) (p.2 ∘ Fin.natAdd 1)) = (p.1,p.2)
    refine Prod.ext ?_ ?_
    · funext j
      rfl
    · funext j
      cases j using Fin.addCases with
      | left j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        exact (Fin.append_left (fun _ : Fin 1 => rv v) (p.2 ∘ Fin.natAdd 1) (0 : Fin 1)).trans hv
      | right j => exact Fin.append_right (fun _ : Fin 1 => rv v) (p.2 ∘ Fin.natAdd 1) j

end IntegrationInACVF.Section7
