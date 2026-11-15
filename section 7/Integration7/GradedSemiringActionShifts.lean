import Integration7.GradedSemiringActions

/-! A fixed shift of homogeneous function degrees retains the actual
graded semiring action. Only arithmetic transports are introduced. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {A F : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (F j)]
variable [DirectSum.GSemiring A]

def gradedDegreeAddEquiv {i j : ℕ} (h : i=j) : F i ≃+ F j := by
  cases h
  exact AddEquiv.refl _

theorem graded_degree_add_equiv_heq {i j : ℕ} (h : i=j) (f : F i) :
    HEq (gradedDegreeAddEquiv h f) f := by
  cases h
  rfl

def gradedShiftComponentAction (B : GradedSemiringAction A F) (s i j : ℕ) :
    A i →+ ((F (j+s)) →+ F ((i+j)+s)) :=
  (AddMonoidHom.compHom (gradedDegreeAddEquiv (F := F) (Nat.add_assoc i j s).symm).toAddMonoidHom).comp
    (B.act i (j+s))

theorem graded_shift_component_action_heq (B : GradedSemiringAction A F)
    (s i j : ℕ) (a : A i) (f : F (j+s)) :
    HEq (gradedShiftComponentAction B s i j a f) (B.act i (j+s) a f) :=
  graded_degree_add_equiv_heq (Nat.add_assoc i j s).symm _

theorem graded_action_apply_heq (B : GradedSemiringAction A F) (i : ℕ) (a : A i)
    {j k : ℕ} (h : j=k) {f : F j} {g : F k} (hf : HEq f g) :
    HEq (B.act i j a f) (B.act i k a g) := by
  cases h
  cases hf
  rfl

def GradedSemiringAction.shift (B : GradedSemiringAction A F) (s : ℕ) :
    GradedSemiringAction A (fun j => F (j+s)) where
  act := gradedShiftComponentAction B s
  one_act j f := (graded_shift_component_action_heq B s 0 j _ f).trans (B.one_act (j+s) f)
  mul_act i j k a b f := by
    have hL := graded_shift_component_action_heq B s (i+j) k (GradedMonoid.GMul.mul a b) f
    have hR := graded_shift_component_action_heq B s i (j+k) a (gradedShiftComponentAction B s j k b f)
    have hC := graded_action_apply_heq B i a (Nat.add_assoc j k s)
      (graded_shift_component_action_heq B s j k b f)
    exact hL.trans ((B.mul_act i j (k+s) a b f).trans (hC.symm.trans hR.symm))
end IntegrationInACVF.Section7
