module

public import IntegrationSection3.ImaginaryParameters

@[expose] public section

/-! Restore global code invariance after promoting real constants to
free variables,by quantifying every representative of the same imaginary.
This generalizes the checked MIT Gamma support-hull argument in the pinned
Section3/GammaBaseTools.lean to any definable quotient presentation. -/

set_option backward.isDefEq.respectTransparency false

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.CodeSupportHull

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {η : Type w''} {β : Type w₁} {α : Type w₂}

def hull (p : Presentation M I η) (R : Set (β ⊕ (η ⊕ α) → M)) : I → Set (β ⊕ α → M) :=
  fun i => {z | ∀ c : p.codes, p.decode c = i →
    Sum.elim (z ∘ Sum.inl) (Sum.elim c.val (z ∘ Sum.inr)) ∈ R}

theorem definable [Finite η] {p : Presentation M I η} {S : Set M}
    (hp : p.IsDefinable L S) {R : Set (β ⊕ (η ⊕ α) → M)} (hR : S.Definable L R) :
    S.Definable L (vectorPullback p (hull p R)) := by
  let πe : η ⊕ η → (η ⊕ (β ⊕ α)) ⊕ η :=
    Sum.elim (fun k => .inl (.inl k)) Sum.inr
  let πR : β ⊕ (η ⊕ α) → (η ⊕ (β ⊕ α)) ⊕ η :=
    Sum.elim (fun b => .inl (.inr (.inl b)))
      (Sum.elim Sum.inr (fun a => .inl (.inr (.inr a))))
  have hall := ((hp.2.preimage_comp πe).himp (hR.preimage_comp πR)).forall_of_finite
  have hc := hp.1.preimage_comp (Sum.inl : η → η ⊕ (β ⊕ α))
  have hReal (z : η ⊕ (β ⊕ α) → M) (c : η → M) :
      Sum.elim z c ∘ πR =
        Sum.elim (z ∘ Sum.inr ∘ Sum.inl) (Sum.elim c (z ∘ Sum.inr ∘ Sum.inr)) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> rfl
  convert hc.inter hall using 1
  ext z
  simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_himp_iff,hReal]
  change (∃ hc : z ∘ Sum.inl ∈ p.codes,
    ∀ c : p.codes, p.decode c = p.decode ⟨z ∘ Sum.inl,hc⟩ →
      Sum.elim (z ∘ Sum.inr ∘ Sum.inl) (Sum.elim c.val (z ∘ Sum.inr ∘ Sum.inr)) ∈ R) ↔
    (z ∘ Sum.inl ∈ p.codes ∧ ∀ c : η → M,
      (∃ hc : z ∘ Sum.inl ∈ p.codes, ∃ hd : c ∈ p.codes,
        p.decode ⟨z ∘ Sum.inl,hc⟩ = p.decode ⟨c,hd⟩) →
      Sum.elim (z ∘ Sum.inr ∘ Sum.inl) (Sum.elim c (z ∘ Sum.inr ∘ Sum.inr)) ∈ R)
  constructor
  · rintro ⟨hc,hall⟩
    exact ⟨hc,fun c ⟨_,hd,he⟩ => hall ⟨c,hd⟩ he.symm⟩
  · rintro ⟨hc,hall⟩
    exact ⟨hc,fun c he => hall c.val ⟨hc,c.property,he.symm⟩⟩

theorem specializes (p : Presentation M I η) (R : Set (β ⊕ (η ⊕ α) → M))
    (Q : I → Set (α → M)) (a : β → M)
    (hAt : ∀ (c : p.codes) (x : α → M),
      Sum.elim a (Sum.elim c.val x) ∈ R ↔ x ∈ Q (p.decode c)) (i : I) (x : α → M) :
    Sum.elim a x ∈ hull p R i ↔ x ∈ Q i := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := p.onto i
    have hx := (hAt c x).mp (h c hc)
    exact hc ▸ hx
  · intro hx c hc
    exact (hAt c x).mpr (hc.symm ▸ hx)

end IntegrationInACVF.Section3.CodeSupportHull
