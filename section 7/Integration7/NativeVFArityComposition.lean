import Integration7.GammaSelectedRVVFTailHeadPreparations

/-! VF arity transports compose and commute with head images. The
back map is a genuine definable bijection with literal coordinate values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m l a b : ℕ}

theorem native_vf_arity_cast_trans (h : n = m) (g : m = l) (A : DefSet (M := M) S n a) :
    nativeVFArityCast g (nativeVFArityCast h A) = nativeVFArityCast (h.trans g) A := by
  cases h
  cases g
  rfl

theorem native_vf_arity_cast_head_image (h : n = m) (A : DefSet (M := M) S (n+1) a) :
    headImage (nativeVFArityCast (congrArg Nat.succ h) A) = nativeVFArityCast h (headImage A) := by
  cases h
  rfl

def nativeVFArityBackMap (h : n = m) (A : DefSet (M := M) S n a) :
    Map (nativeVFArityCast h A) A := by
  cases h
  exact Map.id A

theorem native_vf_arity_back_map_value (h : n = m) (A : DefSet (M := M) S n a)
    (p : nativeVFArityCast h A) :
    (nativeVFArityBackMap h A p).val = (p.val.1 ∘ finCongr h,p.val.2) := by
  cases h
  rfl

theorem native_vf_arity_back_map_bijective (h : n = m) (A : DefSet (M := M) S n a) :
    Function.Bijective (nativeVFArityBackMap h A) := by
  cases h
  exact Function.bijective_id

theorem native_vf_arity_cast_map_back (h : n = m)
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b} (f : Map A B)
    (p : nativeVFArityCast h A) :
    nativeVFArityBackMap h B (nativeVFArityCastMap h f p) = f (nativeVFArityBackMap h A p) := by
  cases h
  rfl

end IntegrationInACVF.Section7
