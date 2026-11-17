module

public import Integration7.GradedSemiringActionShifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A faithful family of additive maps transports the graded action
laws once the actual homogeneous operations commute with those maps. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F G : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [∀ j, AddCommMonoid (G j)] [DirectSum.GSemiring A]

theorem graded_injective_maps_heq (E : ∀ j, G j →+ F j)
    (hE : ∀ j, Function.Injective (E j)) {i j : ℕ} (h : i=j)
    {f : G i} {g : G j} (he : HEq (E i f) (E j g)) : HEq f g := by
  cases h
  exact heq_of_eq (hE i (eq_of_heq he))

def GradedSemiringAction.lift (B : GradedSemiringAction A F)
    (E : ∀ j, G j →+ F j) (hE : ∀ j, Function.Injective (E j))
    (act : ∀ i j, A i →+ (G j →+ G (i+j)))
    (compat : ∀ i j (a : A i) (f : G j), E (i+j) (act i j a f) = B.act i j a (E j f)) :
    GradedSemiringAction A G where
  act := act
  one_act j f := graded_injective_maps_heq E hE (Nat.zero_add j)
    ((heq_of_eq (compat 0 j _ f)).trans (B.one_act j (E j f)))
  mul_act i j k a b f := by
    apply graded_injective_maps_heq E hE (Nat.add_assoc i j k)
    have hL := compat (i+j) k (GradedMonoid.GMul.mul a b) f
    have hR := compat i (j+k) a (act j k b f)
    have hC := congrArg (B.act i (j+k) a) (compat j k b f)
    exact (heq_of_eq hL).trans ((B.mul_act i j k a b (E k f)).trans
      ((heq_of_eq hC).symm.trans (heq_of_eq hR).symm))
end IntegrationInACVF.Section7
