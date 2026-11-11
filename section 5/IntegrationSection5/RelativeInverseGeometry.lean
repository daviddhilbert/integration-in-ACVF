import IntegrationSection5.HeadPreparation
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection5.UnaryInverseGeometry

/-! The inverse affine geometry of an actual relatively special map comes
from its actual unary fibre special bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

theorem fibreSpecial_inverse_insert (f : Map A B) (hf : Function.Bijective f)
    (i : Fin n) (hi : UnaryRelative f i) (u : Fin n → VF (M := M))
    (T : SpecialBijection (coordinateFibre A i u) (coordinateFibre B i u))
    (hT : ∀ p, T.toMap p = coordinateFibreMap f i hi u p) (b : coordinateFibre B i u) :
    coordinateInsert i u (T.inverseMap b).val =
      (Map.inverse f hf ⟨coordinateInsert i u b.val,b.property⟩).val := by
  let a : A := ⟨coordinateInsert i u (T.inverseMap b).val,(T.inverseMap b).property⟩
  have he : f a = ⟨coordinateInsert i u b.val,b.property⟩ := by
    apply Subtype.ext
    have h := coordinateFibreMap_insert f i hi u (T.inverseMap b)
    rw [← hT,T.apply_inverse] at h
    exact h.symm
  have h := congrArg (Map.inverse f hf) he
  rw [Map.inverse_apply] at h
  exact congrArg (fun z : A => z.val) h

namespace HeadPreparation
variable {A : DefSet (M := M) S (n+1) m}

def inverseMap (T : HeadPreparation A) : Map T.target A := Map.inverse T.map T.bijective

@[simp] theorem inverse_apply (T : HeadPreparation A) (a : A) : T.inverseMap (T.map a) = a :=
  Map.inverse_apply _ _ _

@[simp] theorem apply_inverse (T : HeadPreparation A) (b : T.target) : T.map (T.inverseMap b) = b :=
  Map.apply_inverse _ _ _

theorem inverse_tail (T : HeadPreparation A) (b : T.target) (j : Fin n) :
    vfAt (T.inverseMap b).val j.succ = vfAt b.val j.succ := by
  have h := T.special.choose (T.inverseMap b) j.succ (Fin.succ_ne_zero j)
  rw [T.apply_inverse] at h
  exact h.symm

theorem inverse_labels (T : HeadPreparation A) (a b : T.target) (hl : a.val.2 = b.val.2) :
    (T.inverseMap a).val.2 = (T.inverseMap b).val.2 := by
  funext j
  have ha := specialRelative_oldLabels T.special (T.inverseMap a) j
  have hb := specialRelative_oldLabels T.special (T.inverseMap b) j
  rw [T.apply_inverse] at ha hb
  exact ha.symm.trans ((congrFun hl _).trans hb)

theorem inverse_difference (T : HeadPreparation A) (a b : T.target)
    (ht : TailEq a.val b.val) (hl : a.val.2 = b.val.2) :
    vfAt (T.inverseMap a).val 0-vfAt (T.inverseMap b).val 0 = vfAt a.val 0-vfAt b.val 0 := by
  obtain ⟨hi,hF⟩ := T.special
  let u := b.val.1
  have hb : coordinateInsert 0 u (coordinateProject 0 b.val) = b.val :=
    coordinateInsert_project 0 u b.val (fun _ _ => rfl)
  have ha : coordinateInsert 0 u (coordinateProject 0 a.val) = a.val := by
    apply coordinateInsert_project
    intro j hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j => exact ht j
  let x : coordinateFibre T.target 0 u := ⟨coordinateProject 0 a.val,by
    change coordinateInsert 0 u (coordinateProject 0 a.val) ∈ carrier T.target
    rw [ha]
    exact a.property⟩
  let y : coordinateFibre T.target 0 u := ⟨coordinateProject 0 b.val,by
    change coordinateInsert 0 u (coordinateProject 0 b.val) ∈ carrier T.target
    rw [hb]
    exact b.property⟩
  obtain ⟨F,hF⟩ := hF u
  have hx := fibreSpecial_inverse_insert T.map T.bijective 0 hi u F hF x
  have hy := fibreSpecial_inverse_insert T.map T.bijective 0 hi u F hF y
  have hax : (⟨coordinateInsert 0 u x.val,x.property⟩ : T.target) = a := Subtype.ext ha
  have hby : (⟨coordinateInsert 0 u y.val,y.property⟩ : T.target) = b := Subtype.ext hb
  rw [hax] at hx
  rw [hby] at hy
  have hx0 := congrArg (fun p : Point (M := M) (n+1) m => vfAt p 0) hx
  have hy0 := congrArg (fun p : Point (M := M) (n+1) m => vfAt p 0) hy
  simp only [coordinateInsert,vfAt,Function.update_self] at hx0 hy0
  change vfAt (F.inverseMap x).val 0 = vfAt (T.inverseMap a).val 0 at hx0
  change vfAt (F.inverseMap y).val 0 = vfAt (T.inverseMap b).val 0 at hy0
  have h := inverse_special_difference F x y hl
  rw [hx0,hy0] at h
  exact h

end HeadPreparation
end IntegrationInACVF.Section5
