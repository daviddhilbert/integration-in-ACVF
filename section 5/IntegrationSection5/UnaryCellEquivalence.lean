import IntegrationSection5.UnaryInverseGeometry

/-! The actual open-to-open geometry restricted to two fixed RV cells.
The conditions are geometric statements about all subsets, not a
replacement for the special-bijection existence conclusion in 5.2. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {C : DefSet (M := M) S 1 r}

def CellwiseOpenEquivalence (f : A → B) : Prop :=
  ∀ E : Set (Point (M := M) 1 m), E ⊆ carrier A →
    (∃ a : A, ∀ p ∈ E, SameRV p a.val) →
    (∃ b : B, ∀ q ∈ unaryImage f E, SameRV q b.val) →
    (IsUnaryOpenPolydisc E ↔ IsUnaryOpenPolydisc (unaryImage f E))

theorem cellwiseOpenEquivalence_open (f : A → B) (hc : Contractible f)
    (h : CellwiseOpenEquivalence f) : CellwiseOpenMap f := by
  intro E hE hEA hcell
  obtain ⟨a, ha⟩ := hcell
  apply (h E hEA ⟨a, ha⟩ ⟨f a, ?_⟩).mp hE
  rintro q ⟨b, hb, rfl⟩
  exact hc b a (ha b.val hb)

theorem unaryImage_inverse_apply (f : Map A B) (hf : Function.Bijective f)
    (E : Set (Point (M := M) 1 m)) (hEA : E ⊆ carrier A) :
    unaryImage (Map.inverse f hf) (unaryImage f E) = E := by
  ext p
  constructor
  · rintro ⟨b, ⟨a, ha, he⟩, hp⟩
    have hab : f a = b := Subtype.ext he
    rw [← hab, Map.inverse_apply] at hp
    exact hp ▸ ha
  · intro hp
    let a : A := ⟨p, hEA hp⟩
    exact ⟨f a, ⟨a, hp, rfl⟩, congrArg Subtype.val (Map.inverse_apply f hf a)⟩

theorem unaryImage_apply_inverse (f : Map A B) (hf : Function.Bijective f)
    (E : Set (Point (M := M) 1 l)) (hEB : E ⊆ carrier B) :
    unaryImage f (unaryImage (Map.inverse f hf) E) = E := by
  ext p
  constructor
  · rintro ⟨a, ⟨b, hb, he⟩, hp⟩
    have hba : Map.inverse f hf b = a := Subtype.ext he
    rw [← hba, Map.apply_inverse] at hp
    exact hp ▸ hb
  · intro hp
    let b : B := ⟨p, hEB hp⟩
    exact ⟨Map.inverse f hf b, ⟨b, hp, rfl⟩, congrArg Subtype.val (Map.apply_inverse f hf b)⟩

theorem cellwiseOpenEquivalence_inverse (f : Map A B) (hf : Function.Bijective f)
    (h : CellwiseOpenEquivalence f) : CellwiseOpenEquivalence (Map.inverse f hf) := by
  intro E hEB hBcell hAcell
  have he := unaryImage_apply_inverse f hf E hEB
  have htarget : ∃ b : B, ∀ q ∈ unaryImage f (unaryImage (Map.inverse f hf) E), SameRV q b.val :=
    he.symm ▸ hBcell
  have hh := h _ (unaryImage_subset (Map.inverse f hf) E) hAcell htarget
  rw [he] at hh
  exact hh.symm

theorem inverse_special_open_iff (T : SpecialBijection A B) (b : B)
    (E : Set (Point (M := M) 1 l)) (hEB : E ⊆ carrier B)
    (hlabel : ∀ p ∈ E, p.2 = b.val.2) :
    IsUnaryOpenPolydisc E ↔ IsUnaryOpenPolydisc (unaryImage T.inverseMap E) := by
  rw [inverse_special_image_eq T b E hEB hlabel]
  exact unaryReframe_open_iff _ _ b.val.2 E hlabel

end IntegrationInACVF.Section5
