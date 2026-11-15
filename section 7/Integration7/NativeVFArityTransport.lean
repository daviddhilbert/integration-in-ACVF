import Integration7.GammaSelectedRVVFTailMaps
import IntegrationSection5.RelativeSpecial

/-! Transport native mixed domains and their actual maps along a VF
arity equality. Coordinate fibres and relative specialness are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a b : ℕ}

def nativeVFArityCast (h : n = m) (A : DefSet (M := M) S n a) : DefSet (M := M) S m a := h ▸ A

theorem native_vf_arity_cast_carrier (h : n = m) (A : DefSet (M := M) S n a)
    (p : Point (M := M) m a) :
    p ∈ carrier (nativeVFArityCast h A) ↔ (p.1 ∘ finCongr h,p.2) ∈ carrier A := by
  cases h
  rfl

def nativeVFArityCastMap (h : n = m) {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) : Map (nativeVFArityCast h A) (nativeVFArityCast h B) := by
  cases h
  exact f

theorem native_vf_arity_cast_map_bijective (h : n = m)
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (nativeVFArityCastMap h f) := by
  cases h
  exact hf

theorem native_vf_arity_cast_coordinate_fibre (h : n = m) (A : DefSet (M := M) S n a)
    (i : Fin m) (u : Fin m → VF (M := M)) :
    carrier (coordinateFibre (nativeVFArityCast h A) i u) =
      carrier (coordinateFibre A (finCongr h.symm i) (u ∘ finCongr h)) := by
  cases h
  rfl

theorem native_vf_arity_cast_special_relative (h : n = m)
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (i : Fin n) (hf : SpecialRelative f i) :
    SpecialRelative (nativeVFArityCastMap h f) (finCongr h i) := by
  cases h
  exact hf

end IntegrationInACVF.Section7
