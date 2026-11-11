import IntegrationSection4.InverseBodies
import IntegrationSection4.Cells

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseOneCells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def typedBody (T : SpecialBijection A B) (b : B) : Set (VF (M := M)) :=
  {x | x.val ∈ InverseBodies.body T b}

theorem raw_typedBody (T : SpecialBijection A B) (b : B) :
    Cells.rawSet (typedBody T b) = InverseBodies.body T b := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    have hx' := hx
    obtain ⟨a,ha,_⟩ := hx'
    have hVF : iVF x := ha ▸ (vfAt a.val 0).property
    exact ⟨⟨x,hVF⟩,hx,rfl⟩

theorem rv_constant (T : SpecialBijection A B) (b : B)
    (x : VF (M := M)) (hx : x ∈ typedBody T b) :
    rv x = rv (vfAt (T.inverseMap b).val 0) := by
  obtain ⟨a,ha,he⟩ := hx
  have hh := ((sameRV_iff _ _).mp (T.inverse_contractible (T.toMap a) b he)).1 0
  rw [T.inverse_apply] at hh
  change rv (vfAt a.val 0) = rv (vfAt (T.inverseMap b).val 0) at hh
  have hax : vfAt a.val 0 = x := Subtype.ext ha
  rwa [hax] at hh

theorem one_cell (T : SpecialBijection A B) (hB : IsRVPullback (carrier B)) (b : B) :
    Cells.IsOneCell (typedBody T b) := by
  by_cases hb : vfAt b.val 0 = 0
  · left
    refine ⟨vfAt (T.inverseMap b).val 0,Set.ext fun x => ?_⟩
    change (x.val ∈ InverseBodies.body T b) ↔ x = vfAt (T.inverseMap b).val 0
    rw [InverseBodies.body_zero T b hb]
    exact ⟨Subtype.ext,congrArg Subtype.val⟩
  · right
    obtain ⟨γ,_,hBody⟩ := InverseBodies.body_ordinary T hB b hb
    refine ⟨?_,rv (vfAt (T.inverseMap b).val 0),fun x hx => rv_constant T b x hx⟩
    rw [raw_typedBody,hBody]
    exact Or.inr ⟨_,γ,rfl⟩

end IntegrationInACVF.Section4.InverseOneCells
