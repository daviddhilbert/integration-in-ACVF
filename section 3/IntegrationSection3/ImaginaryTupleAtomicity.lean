module

public import IntegrationSection3.AdjoinParameters

@[expose] public section

/-! Atomicity in finite real tuple arities over an interpreted base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3.ImaginaryParameters

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}

def IsAtomicTupleOver (p : Presentation M I κ) (B : Base M I) {υ : Type w₁}
    (A : Set (υ → M)) : Prop :=
  OverBase (L := L) p B A ∧
    ∀ C : Set (υ → M), OverBase (L := L) p B C → A ⊆ C ∨ Disjoint A C

variable {p : Presentation M I κ} {B : Base M I}

theorem isAtomicTupleOver_empty_iff [Finite κ] {υ : Type w₁} [Finite υ]
    {A : Set (υ → M)} (hB : B.imaginary = ∅) :
    IsAtomicTupleOver (L := L) p B A ↔ IsAtomic L B.real A := by
  constructor
  · rintro ⟨hA,hall⟩
    exact ⟨(OverBase.empty_iff_real hB).mp hA,
      fun C hC => hall C ((OverBase.empty_iff_real hB).mpr hC)⟩
  · rintro ⟨hA,hall⟩
    exact ⟨(OverBase.empty_iff_real hB).mpr hA,
      fun C hC => hall C ((OverBase.empty_iff_real hB).mp hC)⟩

theorem unary_tuple_atomic_iff {A : Set M} :
    IsAtomicTupleOver (L := L) p B {z : Fin 1 → M | z 0 ∈ A} ↔
      IsAtomicOver (L := L) p B A := by
  constructor
  · rintro ⟨hA,hall⟩
    refine ⟨hA,?_⟩
    intro S hS
    rcases hall {z | z 0 ∈ S} hS with hw | hd
    · exact Or.inl (fun x hx => hw (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ A} from hx))
    · exact Or.inr (Set.disjoint_left.mpr fun x hxA hxS => Set.disjoint_left.mp hd
        (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ A} from hxA)
        (show ![x] ∈ {z : Fin 1 → M | z 0 ∈ S} from hxS))
  · rintro ⟨hA,hall⟩
    refine ⟨hA,?_⟩
    intro C hC
    let S : Set M := {x | ![x] ∈ C}
    have he : {z : Fin 1 → M | z 0 ∈ S} = C := by
      ext z
      have hz : ![z 0] = z := by funext j; fin_cases j; rfl
      change ![z 0] ∈ C ↔ z ∈ C
      rw [hz]
    have hS : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S} := he.symm ▸ hC
    rcases hall S hS with hw | hd
    · left
      intro z hz
      have hmem : ![z 0] ∈ C := hw hz
      have heq : ![z 0] = z := by funext j; fin_cases j; rfl
      rwa [heq] at hmem
    · right
      apply Set.disjoint_left.mpr
      intro z hzA hzC
      have hzS : z 0 ∈ S := by
        change ![z 0] ∈ C
        have heq : ![z 0] = z := by funext j; fin_cases j; rfl
        rw [heq]
        exact hzC
      exact Set.disjoint_left.mp hd hzA hzS

end IntegrationInACVF.Section3.ImaginaryParameters
