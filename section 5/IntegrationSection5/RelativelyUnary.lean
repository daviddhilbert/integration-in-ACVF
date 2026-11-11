import Section5.Core

/-! Definition 5.4: preserve all VF coordinates except the indicated one.
RV labels may change, as they do under canonical bijections. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
variable {C : DefSet (M := M) S n k}

def UnaryRelative (f : A → B) (i : Fin n) : Prop :=
  ∀ a : A, ∀ j : Fin n, j ≠ i → (f a).val.1 j = a.val.1 j

def RelativelyUnary (f : A → B) : Prop := ∃ i, UnaryRelative f i

theorem unaryRelative_id (i : Fin n) : UnaryRelative (Map.id A) i :=
  fun _ _ _ => rfl

theorem unaryRelative_comp {f : A → B} {g : B → C} {i : Fin n}
    (hf : UnaryRelative f i) (hg : UnaryRelative g i) : UnaryRelative (g ∘ f) i :=
  fun a j hj => (hg (f a) j hj).trans (hf a j hj)

theorem unaryRelative_inverse (f : Map A B) (hf : Function.Bijective f)
    {i : Fin n} (hi : UnaryRelative f i) : UnaryRelative (Map.inverse f hf) i := by
  intro b j hj
  have h := hi (Map.inverse f hf b) j hj
  rw [Map.apply_inverse] at h
  exact h.symm

theorem relativelyUnary_inverse (f : Map A B) (hf : Function.Bijective f)
    (hi : RelativelyUnary f) : RelativelyUnary (Map.inverse f hf) := by
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, unaryRelative_inverse f hf hi⟩

theorem unaryRelative_one {A : DefSet (M := M) S 1 m}
    {B : DefSet (M := M) S 1 l} (f : A → B) : UnaryRelative f 0 := by
  intro a j hj
  exact (hj (Subsingleton.elim j 0)).elim

theorem canonical_unaryRelative (A : DefSet (M := M) S n m) (i : Fin n) :
    UnaryRelative (SpecialBijection.canonical A).toMap i := by
  intro a j hj
  rfl

end IntegrationInACVF.Section5
