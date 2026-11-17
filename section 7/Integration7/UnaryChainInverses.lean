module

public import IntegrationSection5.UnaryFactorizations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual inverse unary chains, retaining the original real parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5.UnaryChain
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

def inverse {a b : ℕ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b} :
    UnaryChain S n A B → UnaryChain S n B A
  | .nil A => .nil A
  | @UnaryChain.cons _ _ _ _ _ a c b A W B i f hf hi tail =>
    tail.inverse.append (.cons i (Map.inverse f hf) (Equiv.ofBijective f hf).symm.bijective
      (unaryRelative_inverse f hf hi) (.nil A))

theorem inverse_apply {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : UnaryChain S n A B) : ∀ p : B, T.toMap (T.inverse.toMap p) = p := by
  induction T with
  | nil A => intro p; rfl
  | @cons a c b A W B i f hf hi tail ih =>
    intro p
    change tail.toMap (f ((tail.inverse.append (.cons i (Map.inverse f hf)
      (Equiv.ofBijective f hf).symm.bijective (unaryRelative_inverse f hf hi) (.nil A))).toMap p)) = p
    rw [append_toMap]
    change tail.toMap (f (Map.inverse f hf (tail.inverse.toMap p))) = p
    rw [Map.apply_inverse]
    exact ih p

theorem inverse_to_map {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : UnaryChain S n A B) : T.inverse.toMap = Map.inverse T.toMap T.bijective := by
  apply Map.ext
  intro p
  apply T.bijective.injective
  exact (T.inverse_apply p).trans (Map.apply_inverse T.toMap T.bijective p).symm

end IntegrationInACVF.Section5.UnaryChain
