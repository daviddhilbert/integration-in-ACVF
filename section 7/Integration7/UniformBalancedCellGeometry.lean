module

public import Integration7.UniformCellPositionRows

@[expose] public section

/-! Uniform consequences of the balanced-row case. The one global
centre is injective in the other VF coordinate on each refinement label,
and its image covers every actual head value of that labelled cell. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m : ℕ}
variable {G : Base (M := M)} {A : Set (Point (M := M) 2 m)}

namespace UniformMixedCellPresentation

def BalancedRows (F : UniformMixedCellPresentation G A) : Prop :=
  ∀ a : A, ∃ r : RV (M := M), Cells.IsBalanced (mixedPairFibre F.parameters a) (F.localPosition a) r
    ((F.vertical.projection a).val.2 F.vertical.paradigm_index)

private theorem own_pair_mem (F : UniformMixedCellPresentation G A) (a : A) :
    (vfAt a.val 1,vfAt a.val 0) ∈ mixedPairFibre F.parameters a := by
  refine ⟨a,?_,rfl⟩
  funext i
  fin_cases i <;> rfl

theorem balanced_centre_injective (F : UniformMixedCellPresentation G A) (hBalanced : F.BalancedRows)
    (a b : A) (hP : F.parameters.toFun b = F.parameters.toFun a) (hCentre : F.centre a = F.centre b) :
    vfAt a.val 1 = vfAt b.val 1 := by
  obtain ⟨r,hBal⟩ := hBalanced a
  have ha : vfAt a.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) :=
    ⟨_,F.own_pair_mem a,rfl⟩
  have hb : vfAt b.val 1 ∈ Cells.first (mixedPairFibre F.parameters a) := by
    refine ⟨(vfAt b.val 1,vfAt b.val 0),⟨b,?_,hP⟩,rfl⟩
    funext i
    fin_cases i <;> rfl
  have hca := F.centre_eq_local_position a a rfl
  have hcb := F.centre_eq_local_position a b hP
  exact hBal.2.2.1.bijective.2.1 ha hb (hca.symm.trans (hCentre.trans hcb))

theorem balanced_centre_covers_head (F : UniformMixedCellPresentation G A) (hBalanced : F.BalancedRows) (a : A) :
    ∃ b : A, F.parameters.toFun b = F.parameters.toFun a ∧ F.centre b = vfAt a.val 0 := by
  obtain ⟨r,hBal⟩ := hBalanced a
  have ha : vfAt a.val 0 ∈ Cells.second (mixedPairFibre F.parameters a) :=
    ⟨_,F.own_pair_mem a,rfl⟩
  obtain ⟨x,hx,hfx⟩ := hBal.2.2.1.bijective.2.2 ha
  obtain ⟨p,hp,hpx⟩ := hx
  obtain ⟨b,hb,hPb⟩ := hp
  have hbx : vfAt b.val 1 = x := by
    have he := congrFun hb 1
    exact he.trans hpx
  exact ⟨b,hPb,(F.centre_eq_local_position a b hPb).trans ((congrArg (F.localPosition a) hbx).trans hfx)⟩

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
