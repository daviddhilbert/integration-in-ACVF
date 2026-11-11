import IntegrationSection4.GammaRVMaps
import IntegrationSection4.InverseOneCells

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
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m l : ℕ}
variable {A : Set (Point (M := M) 1 m)} {E : Set (Point (M := M) 1 l)}

def specialSource (T : GammaSpecialBijection G A E) (a : A) : T.source :=
  ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mpr a.property⟩

theorem fromSpecial_apply (T : GammaSpecialBijection G A E) (a : A) :
    (fromSpecial T).toFun a = Fin.append
      (fun i => rv (vfAt (T.special.toMap (specialSource T a)).val i))
      (T.special.toMap (specialSource T a)).val.2 := rfl

theorem fromSpecial_eq_iff (T : GammaSpecialBijection G A E) (a b : A) :
    (fromSpecial T).toFun a = (fromSpecial T).toFun b ↔
      SameRV (T.special.toMap (specialSource T a)).val (T.special.toMap (specialSource T b)).val := by
  rw [fromSpecial_apply,fromSpecial_apply,sameRV_iff]
  constructor
  · intro he
    refine ⟨fun i => ?_,funext fun i => ?_⟩
    · have hh := congrFun he (Fin.castAdd l i)
      simpa only [Fin.append_left,vfAt] using hh
    · have hh := congrFun he (Fin.natAdd 1 i)
      simpa only [Fin.append_right] using hh
  · rintro ⟨hv,hl⟩
    funext i
    cases i using Fin.addCases with
    | left i => simpa only [Fin.append_left,vfAt] using hv i
    | right i => simpa only [Fin.append_right] using congrFun hl i

theorem fromSpecial_reflects_rv (T : GammaSpecialBijection G A E) (a b : A)
    (he : (fromSpecial T).toFun a = (fromSpecial T).toFun b) : SameRV a.val b.val := by
  have hh := T.special.inverse_contractible (T.special.toMap (specialSource T a))
    (T.special.toMap (specialSource T b)) ((fromSpecial_eq_iff T a b).mp he)
  simpa only [T.special.inverse_apply,specialSource] using hh

/-- An actual RV-map fibre is the complete unary inverse piece with
its original context labels fixed. Both containments are proved. -/
theorem fromSpecial_fibre (T : GammaSpecialBijection G A E) (a₀ : A) :
    {p | ∃ a : A, a.val = p ∧ (fromSpecial T).toFun a = (fromSpecial T).toFun a₀} =
      {p | (vfAt p 0).val ∈ InverseBodies.body T.special (T.special.toMap (specialSource T a₀)) ∧
        p.2 = (T.special.inverseMap (T.special.toMap (specialSource T a₀))).val.2} := by
  let b := T.special.toMap (specialSource T a₀)
  ext p
  constructor
  · rintro ⟨a,rfl,he⟩
    have hRV := (fromSpecial_eq_iff T a a₀).mp he
    refine ⟨⟨specialSource T a,rfl,hRV⟩,?_⟩
    have hh := ((sameRV_iff _ _).mp (T.special.inverse_contractible
      (T.special.toMap (specialSource T a)) b hRV)).2
    rw [T.special.inverse_apply] at hh
    exact hh
  · rintro ⟨⟨a,ha,he⟩,hpLabels⟩
    have hLabels : a.val.2 = (T.special.inverseMap b).val.2 := by
      have hh := ((sameRV_iff _ _).mp (T.special.inverse_contractible (T.special.toMap a) b he)).2
      rw [T.special.inverse_apply] at hh
      exact hh
    have hap : a.val = p := by
      apply Prod.ext
      · funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact Subtype.ext ha
      · exact hLabels.trans hpLabels.symm
    let aA : A := ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mp a.property⟩
    refine ⟨aA,hap,(fromSpecial_eq_iff T aA a₀).mpr ?_⟩
    exact he

end IntegrationInACVF.Section4.GammaRVMap
