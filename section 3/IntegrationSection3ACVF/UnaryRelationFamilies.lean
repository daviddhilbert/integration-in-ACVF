import IntegrationSection3ACVF.FullBaseDefinability

/-! Full original-base graph operations on parameterized unary relations.
The labels stay free variables and may include source and target contexts. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.UnaryRelationFamilies

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def pair (p : σ → M) (x y : M) : σ ⊕ Fin 2 → M := Sum.elim p ![x,y]

def domain (G : Set (σ ⊕ Fin 2 → M)) : Set (σ ⊕ Fin 1 → M) :=
  {z | ∃ y, pair (z ∘ Sum.inl) (z (.inr 0)) y ∈ G}

def restrict (G : Set (σ ⊕ Fin 2 → M)) (C : Set (σ ⊕ Fin 1 → M)) : Set (σ ⊕ Fin 2 → M) :=
  {z | z ∈ G ∧ Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] ∈ C}

def image (G : Set (σ ⊕ Fin 2 → M)) (C : Set (σ ⊕ Fin 1 → M)) : Set (σ ⊕ Fin 1 → M) :=
  {z | ∃ x, pair (z ∘ Sum.inl) x (z (.inr 0)) ∈ G ∧ Sum.elim (z ∘ Sum.inl) ![x] ∈ C}

def swap (G : Set (σ ⊕ Fin 2 → M)) : Set (σ ⊕ Fin 2 → M) :=
  {z | pair (z ∘ Sum.inl) (z (.inr 1)) (z (.inr 0)) ∈ G}

theorem domain_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G) :
    FullBaseAtomicity.OverBase B (domain G) := by
  let π : σ ⊕ Fin 2 → (σ ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun p => .inl (.inl p)) (![.inl (.inr 0),.inr 0] : Fin 2 → _)
  have he (z : σ ⊕ Fin 1 → M) (y : Fin 1 → M) :
      Sum.elim z y ∘ π = pair (z ∘ Sum.inl) (z (.inr 0)) (y 0) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.preimage_comp hG π)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ y : Fin 1 → M, Sum.elim z y ∘ π ∈ G) ↔ _
  simp_rw [he]
  exact ⟨fun ⟨y,hy⟩ => ⟨y 0,hy⟩,fun ⟨y,hy⟩ => ⟨![y],hy⟩⟩

theorem restrict_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {C : Set (σ ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (restrict G C) := by
  let π : σ ⊕ Fin 1 → σ ⊕ Fin 2 := Sum.map id (fun _ => 0)
  have hd := FullBaseAtomicity.OverBase.inter hG (FullBaseAtomicity.OverBase.preimage_comp hC π)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  have he : z ∘ π = Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k; rfl
  change (z ∈ G ∧ z ∘ π ∈ C) ↔ _
  rw [he]
  rfl

theorem image_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {C : Set (σ ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (image G C) := by
  let πG : σ ⊕ Fin 2 → (σ ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun p => .inl (.inl p)) (![.inr 0,.inl (.inr 0)] : Fin 2 → _)
  let πC : σ ⊕ Fin 1 → (σ ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun p => .inl (.inl p)) (fun _ => .inr 0)
  have heG (z : σ ⊕ Fin 1 → M) (x : Fin 1 → M) :
      Sum.elim z x ∘ πG = pair (z ∘ Sum.inl) (x 0) (z (.inr 0)) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have heC (z : σ ⊕ Fin 1 → M) (x : Fin 1 → M) :
      Sum.elim z x ∘ πC = Sum.elim (z ∘ Sum.inl) ![x 0] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k; rfl
  have hd := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp hG πG)
      (FullBaseAtomicity.OverBase.preimage_comp hC πC))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ x : Fin 1 → M, Sum.elim z x ∘ πG ∈ G ∧ Sum.elim z x ∘ πC ∈ C) ↔ _
  simp_rw [heG,heC]
  exact ⟨fun ⟨x,hxG,hxC⟩ => ⟨x 0,hxG,hxC⟩,fun ⟨x,hxG,hxC⟩ => ⟨![x],hxG,hxC⟩⟩

theorem swap_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G) :
    FullBaseAtomicity.OverBase B (swap G) := by
  let π : σ ⊕ Fin 2 → σ ⊕ Fin 2 := Sum.map id (![1,0] : Fin 2 → Fin 2)
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.preimage_comp hG π)
  intro z
  have he : z ∘ π = pair (z ∘ Sum.inl) (z (.inr 1)) (z (.inr 0)) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  change (z ∘ π ∈ G) ↔ _
  rw [he]
  rfl

end IntegrationInACVF.Section3ACVF.UnaryRelationFamilies
