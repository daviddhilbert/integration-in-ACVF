import Integration7.NativeVFProjectionDomains
import Integration7.FixedLabelsVFPermutations

/-! Exact native fibre descriptions of the two product images of a
balanced cell, using the cell's actual unary projection domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 IntegrationInACVF.Section5
open IntegrationInACVF.Section6
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem native_rv_class_product_fibre_condition
    (X Z : DefSet (M := M) S 2 0) (r : RV (M := M))
    (hX : nativeVFPairDomain X = {x | rv x = r} ×ˢ second (nativeVFPairDomain Z)) :
    ∀ p : Point (M := M) 2 0, p ∈ carrier X ↔ rv (vfAt p 0) = r ∧
      ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier (nativeVFProjectionDomain Z 1) := by
  intro p
  have hP := mem_native_vf_pair_domain X p
  rw [hX] at hP
  change (rv (vfAt p 0) = r ∧ vfAt p 1 ∈ second (nativeVFPairDomain Z)) ↔ p ∈ carrier X at hP
  exact hP.symm.trans (and_congr Iff.rfl (native_vf_second_projection Z ((fun _ => vfAt p 1),Fin.elim0)).symm)

theorem native_product_rv_class_swapped_fibre_condition
    (Y Z : DefSet (M := M) S 2 0) (t : RV (M := M))
    (hY : nativeVFPairDomain Y = first (nativeVFPairDomain Z) ×ˢ {x | rv x = t}) :
    ∀ p : Point (M := M) 2 0, p ∈ carrier (vfPermutationImage Y (Equiv.swap 0 1)) ↔
      rv (vfAt p 0) = t ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier (nativeVFProjectionDomain Z 0) := by
  intro p
  have h0 := vfPermutationImage_row Y (Equiv.swap 0 1) p.1 p.2
  have hP := mem_native_vf_pair_domain Y (p.1 ∘ (Equiv.swap 0 1).symm,p.2)
  rw [hY] at hP
  change ((p.1 ∘ (Equiv.swap 0 1).symm) 0 ∈ first (nativeVFPairDomain Z) ∧
    rv ((p.1 ∘ (Equiv.swap 0 1).symm) 1) = t) ↔
      (p.1 ∘ (Equiv.swap 0 1).symm,p.2) ∈ carrier Y at hP
  simp only [Function.comp_apply,Equiv.symm_swap,Equiv.swap_apply_left,Equiv.swap_apply_right] at hP
  have h1 := h0.trans hP.symm
  have hD := native_vf_first_projection Z ((fun _ : Fin 1 => vfAt p 1),Fin.elim0)
  exact h1.trans ⟨fun h => ⟨h.2,hD.mpr h.1⟩,fun h => ⟨hD.mp h.2,h.1⟩⟩

end IntegrationInACVF.Section7
