import Section4.Products

/-! A map constant on the fibres of a definable map descends to its actual
image. The entire descended graph remains over the original parameter set.
Representative choices are internal and introduce no named parameters. -/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section4.DefinableDescent

variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M}
variable {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

def representative (q : Map A B) (u : q.image) : A :=
  Classical.choose u.property

theorem representative_spec (q : Map A B) (u : q.image) :
    (q (representative q u)).val = u.val := Classical.choose_spec u.property

def descendFun (q : Map A B) (f : Map A C) (u : q.image) : C :=
  f (representative q u)

theorem descendFun_spec (q : Map A B) (f : Map A C)
    (hf : ∀ a b, q a = q b → f a = f b) (a : A) :
    descendFun q f (q.toImage a) = f a := by
  apply hf
  exact Subtype.ext (representative_spec q (q.toImage a))

def descendMap (q : Map A B) (f : Map A C)
    (hf : ∀ a b, q a = q b → f a = f b) : Map q.image C where
  toFun := descendFun q f
  graph_definable := by
    have h := (q.graph_definable.swap P Q).comp Q P R f.graph_definable
    apply h.congr Q R
    intro u z
    constructor
    · rintro ⟨x, ⟨a, ha, hqa⟩, ⟨b, hb, hfb⟩⟩
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      let v : q.image := ⟨u, a, hqa⟩
      refine ⟨v, rfl, ?_⟩
      have hv : v = q.toImage a := Subtype.ext hqa.symm
      rw [hv, descendFun_spec q f hf]
      exact hfb
    · rintro ⟨v, rfl, hz⟩
      exact ⟨(representative q v).val,
        ⟨representative q v, rfl, representative_spec q v⟩,
        ⟨representative q v, rfl, hz⟩⟩

theorem descendMap_spec (q : Map A B) (f : Map A C)
    (hf : ∀ a b, q a = q b → f a = f b) (a : A) :
    descendMap q f hf (q.toImage a) = f a := descendFun_spec q f hf a

theorem descendMap_unique (q : Map A B) (f : Map A C)
    (hf : ∀ a b, q a = q b → f a = f b)
    (g : Map q.image C) (hg : ∀ a, g (q.toImage a) = f a) :
    g = descendMap q f hf := by
  apply Map.ext
  intro u
  have hu : q.toImage (representative q u) = u := Subtype.ext (representative_spec q u)
  rw [← hu, hg, descendMap_spec q f hf]

end IntegrationInACVF.Section4.DefinableDescent
