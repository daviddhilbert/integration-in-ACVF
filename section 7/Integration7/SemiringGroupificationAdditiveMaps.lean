import Integration7.SemiringGroupificationGrothendieck

/-! Additive maps on a semiring extend through the actual universal
ring groupification, without requiring a multiplicative target. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {R : Type u} [Semiring R] {A : Type v} [AddCommGroup A]

def semiringGroupificationAdditiveLift (f : R →+ A) : SemiringGroupification R →+ A :=
  (Algebra.GrothendieckAddGroup.lift f).comp
    (semiringGroupificationGrothendieckEquiv R).toAddMonoidHom

theorem semiring_groupification_additive_lift_of (f : R →+ A) (a : R) :
    semiringGroupificationAdditiveLift f (semiringGroupificationOf R a)=f a := by
  change Algebra.GrothendieckAddGroup.lift f
    (semiringGroupificationLift Algebra.GrothendieckAddGroup.ofRingHom (semiringGroupificationOf R a))=f a
  rw [semiringGroupificationLift_of]
  exact Algebra.GrothendieckAddGroup.lift_apply_of f a

theorem semiring_groupification_additive_hom_ext {f g : SemiringGroupification R →+ A}
    (h : ∀ a, f (semiringGroupificationOf R a)=g (semiringGroupificationOf R a)) : f=g := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference x
  rw [map_sub,map_sub,h,h]
end IntegrationInACVF.Section7
