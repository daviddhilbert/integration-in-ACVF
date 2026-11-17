module

public import IntegrationSection3ACVF.GammaDifferenceRealization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A bijection between two genuine open balls that multiplies all
difference values by one Gamma factor multiplies their radii by that factor.
The proof compares the realized difference cuts, including both directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_linear_open_ball_radii
    (a b : VFType (M := M)) (α β s : Values.Gamma (M := M))
    (F : {x : VFType (M := M) | x.val ∈ gammaBall a α true} →
      {y : VFType (M := M) | y.val ∈ gammaBall b β true})
    (hF : Function.Surjective F)
    (hLin : ∀ x y, Values.vfValueHom ((F y).val-(F x).val) =
      s.val*Values.vfValueHom (y.val-x.val)) : β = s*α := by
  have hs0 : s.val ≠ 0 := fun h => s.property (h.trans Values.infinity_eq_zero.symm)
  have hCut (γ : Values.Gamma (M := M)) : α < γ ↔ β < s*γ := by
    constructor
    · intro hγ
      obtain ⟨x,y,hx,hy,_,hxy⟩ := GammaDifferenceRealization.exists_pair a α γ hγ
      have hOut := GammaDifferenceRealization.difference_gt_radius b β
        (F ⟨x,hx⟩).val (F ⟨y,hy⟩).val (F ⟨x,hx⟩).property (F ⟨y,hy⟩).property
      rw [hLin,hxy] at hOut
      exact hOut
    · intro hγ
      obtain ⟨u,v,hu,hv,_,huv⟩ := GammaDifferenceRealization.exists_pair b β (s*γ) hγ
      obtain ⟨x,hx⟩ := hF ⟨u,hu⟩
      obtain ⟨y,hy⟩ := hF ⟨v,hv⟩
      have hxy := hLin x y
      rw [hx,hy] at hxy
      have hDiff : Values.vfValueHom (y.val-x.val) = γ.val := by
        apply mul_left_cancel₀ hs0
        exact hxy.symm.trans huv
      have hIn := GammaDifferenceRealization.difference_gt_radius a α x.val y.val x.property y.property
      rw [hDiff] at hIn
      exact hIn
  have hLower : s*α ≤ β := le_of_not_gt (fun h => (lt_irrefl α) ((hCut α).mpr h))
  have hUpper : β ≤ s*α := by
    have hn : ¬ α < s⁻¹*β := by
      intro h
      have hh := (hCut (s⁻¹*β)).mp h
      exact (lt_irrefl β) (by simpa only [mul_inv_cancel_left] using hh)
    calc
      β = s*(s⁻¹*β) := (mul_inv_cancel_left s β).symm
      _ ≤ s*α := by
        simpa only [mul_comm] using mul_le_mul_right (le_of_not_gt hn) s
  exact le_antisymm hUpper hLower

end IntegrationInACVF.Section7
