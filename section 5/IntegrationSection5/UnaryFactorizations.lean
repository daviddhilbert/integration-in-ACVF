import IntegrationSection5.RelativelyUnary

/-! Finite compositions of actual definable relatively unary bijections.
This records Definition 5.4's factorization claim for special bijections.
It does not assert the partition theorem for arbitrary bijections (5.6). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive UnaryChain (S : Set M) (n : ℕ) : {m l : ℕ} →
    DefSet (M := M) S n m → DefSet (M := M) S n l → Type where
  | nil {m : ℕ} (A : DefSet (M := M) S n m) : UnaryChain S n A A
  | cons {m l k : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
      {C : DefSet (M := M) S n k} (i : Fin n) (f : Map A B)
      (bijective : Function.Bijective f) (unary : UnaryRelative f i)
      (tail : UnaryChain S n B C) : UnaryChain S n A C

namespace UnaryChain

variable {S : Set M} {n m l k : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
variable {C : DefSet (M := M) S n k}

def toMap {m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} :
    UnaryChain S n A B → Map A B
  | .nil A => Map.id A
  | .cons _ f _ _ tail => Map.comp tail.toMap f

theorem bijective (t : UnaryChain S n A B) : Function.Bijective t.toMap := by
  induction t with
  | nil A => exact Function.bijective_id
  | cons i f hf hi tail ih => exact ih.comp hf

def append {m l k : ℕ} {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} {C : DefSet (M := M) S n k} :
    UnaryChain S n A B → UnaryChain S n B C → UnaryChain S n A C
  | .nil _, u => u
  | .cons i f hf hi tail, u => .cons i f hf hi (tail.append u)

theorem append_toMap (t : UnaryChain S n A B) (u : UnaryChain S n B C) :
    (t.append u).toMap = Map.comp u.toMap t.toMap := by
  induction t with
  | nil A => apply Map.ext; intro a; rfl
  | cons i f hf hi tail ih =>
    apply Map.ext
    intro a
    change (tail.append u).toMap (f a) = _
    rw [ih]
    rfl

end UnaryChain

variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def primitiveUnaryCoordinate (hn : 0 < n) : Primitive S n A B → Fin n
  | .canonical _ => ⟨0, hn⟩
  | @Primitive.centripetal _ _ _ _ _ _ _ j _ _ => j

theorem primitive_unaryRelative (hn : 0 < n) (p : Primitive S n A B) :
    UnaryRelative p.toMap (primitiveUnaryCoordinate hn p) := by
  cases p with
  | canonical A => intro a i hi; rfl
  | centripetal D =>
    intro a i hi
    change (D.toFocusGeometry.eta a.val).1 i = a.val.1 i
    exact D.toFocusGeometry.eta_other a.val i hi

def specialUnaryChain (hn : 0 < n) {m l : ℕ}
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l} :
    Chain S n A B → UnaryChain S n A B
  | .nil A => .nil A
  | .cons p tail => .cons (primitiveUnaryCoordinate hn p) p.toMap p.bijective
      (primitive_unaryRelative hn p) (specialUnaryChain hn tail)

theorem specialUnaryChain_toMap (hn : 0 < n) (t : Chain S n A B) :
    (specialUnaryChain hn t).toMap = t.toMap := by
  induction t with
  | nil A => rfl
  | cons p tail ih =>
    change Map.comp (specialUnaryChain hn tail).toMap p.toMap = Map.comp tail.toMap p.toMap
    rw [ih]

theorem special_bijection_unary_factorization (hn : 0 < n) (T : SpecialBijection A B) :
    ∃ t : UnaryChain S n A B, t.toMap = T.toMap :=
  ⟨specialUnaryChain hn T.chain, specialUnaryChain_toMap hn T.chain⟩

/-- The base case of 5.6 needs no partition refinement: every bijection
with one VF coordinate is itself relatively unary. -/
theorem unary_bijection_factorization {A : DefSet (M := M) S 1 m}
    {B : DefSet (M := M) S 1 l} (f : Map A B) (hf : Function.Bijective f) :
    ∃ t : UnaryChain S 1 A B, t.toMap = f := by
  refine ⟨.cons 0 f hf (unaryRelative_one f) (.nil B), ?_⟩
  apply Map.ext
  intro a
  rfl

end IntegrationInACVF.Section5
