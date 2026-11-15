import Integration7.SemiringGroupificationDifferences
import Section4.Imported.GrothendieckRing

/-! The free-ring groupification agrees with additive Grothendieck
completion for arbitrary semirings, including noncommutative ones.
Equality of positive generators is precisely stable additive equality. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable (R : Type u) [Semiring R]

def semiringGroupificationToGrothendieck :
    SemiringGroupification R →+* Algebra.GrothendieckAddGroup R :=
  semiringGroupificationLift Algebra.GrothendieckAddGroup.ofRingHom

def grothendieckToSemiringGroupification :
    Algebra.GrothendieckAddGroup R →+* SemiringGroupification R :=
  Algebra.GrothendieckAddGroup.liftRingHom (semiringGroupificationOf R)

theorem semiring_groupification_grothendieck_left_inverse :
    Function.LeftInverse (grothendieckToSemiringGroupification R)
      (semiringGroupificationToGrothendieck R) := by
  have h : (grothendieckToSemiringGroupification R).comp
      (semiringGroupificationToGrothendieck R) = RingHom.id _ := by
    apply semiringGroupification_hom_ext
    intro a
    change grothendieckToSemiringGroupification R
      (semiringGroupificationLift _ (semiringGroupificationOf R a)) = _
    rw [semiringGroupificationLift_of]
    exact Algebra.GrothendieckAddGroup.liftRingHom_apply_of _ a
  exact RingHom.congr_fun h

theorem semiring_groupification_grothendieck_right_inverse :
    Function.RightInverse (grothendieckToSemiringGroupification R)
      (semiringGroupificationToGrothendieck R) := by
  have h : (semiringGroupificationToGrothendieck R).comp
      (grothendieckToSemiringGroupification R) = RingHom.id _ := by
    apply Algebra.GrothendieckAddGroup.ringHom_ext
    intro a
    change semiringGroupificationToGrothendieck R
      (Algebra.GrothendieckAddGroup.liftRingHom _ (Algebra.GrothendieckAddGroup.of a)) = _
    rw [Algebra.GrothendieckAddGroup.liftRingHom_apply_of]
    exact semiringGroupificationLift_of _ a
  exact RingHom.congr_fun h

def semiringGroupificationGrothendieckEquiv :
    SemiringGroupification R ≃+* Algebra.GrothendieckAddGroup R :=
  { semiringGroupificationToGrothendieck R with
    invFun := grothendieckToSemiringGroupification R
    left_inv := semiring_groupification_grothendieck_left_inverse R
    right_inv := semiring_groupification_grothendieck_right_inverse R }

theorem semiring_groupification_of_eq_iff (a b : R) :
    semiringGroupificationOf R a = semiringGroupificationOf R b ↔
      ∃ c : R, c+a=c+b := by
  constructor
  · intro h
    have hg := congrArg (semiringGroupificationToGrothendieck R) h
    change semiringGroupificationLift _ _ = semiringGroupificationLift _ _ at hg
    rw [semiringGroupificationLift_of,semiringGroupificationLift_of] at hg
    obtain ⟨c,hc⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid R)).exists_of_eq hg
    exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩
    have h := congrArg (semiringGroupificationOf R) hc
    rw [map_add,map_add] at h
    exact add_left_cancel h
end IntegrationInACVF.Section7
