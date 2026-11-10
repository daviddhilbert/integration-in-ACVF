module

public import IntegrationSection3.ImaginaryBaseFamilies

@[expose] public section

/-! Images and preimages of a map definable only on its stated domain.
All formulas stay over the original interpreted parameter base; values
of a total extension outside the domain play no role. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryBaseImages

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}

def graphOn (A : Set M) (f : M → M) : Set (Fin 2 → M) :=
  {z | z 0 ∈ A ∧ z 1 = f (z 0)}

theorem image_definable {A : Set M} {f : M → M}
    (hf : OverBase (L := L) p B (graphOn A f)) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ f '' A} := by
  have hd := OverBase.exists_block
    (hf.preimage_comp (![.inr 0,.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  convert hd using 1
  ext z
  change (∃ x, x ∈ A ∧ f x = z 0) ↔
    ∃ x : Fin 1 → M, x 0 ∈ A ∧ z 0 = f (x 0)
  exact ⟨fun ⟨x,hx,he⟩ => ⟨![x],hx,he.symm⟩,
    fun ⟨x,hx,he⟩ => ⟨x 0,hx,he.symm⟩⟩

theorem preimage_definable (hp : B.real.Definable L p.codes) {A S : Set M} {f : M → M}
    (hf : OverBase (L := L) p B (graphOn A f))
    (hS : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S}) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A ∧ f (z 0) ∈ S} := by
  have hi := OverBase.inter hf (hS.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))) hp
  have hd := OverBase.exists_block
    (hi.preimage_comp (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  convert hd using 1
  ext z
  change (z 0 ∈ A ∧ f (z 0) ∈ S) ↔
    ∃ y : Fin 1 → M, (z 0 ∈ A ∧ y 0 = f (z 0)) ∧ y 0 ∈ S
  constructor
  · rintro ⟨ha,hs⟩
    exact ⟨![f (z 0)],⟨ha,rfl⟩,hs⟩
  · rintro ⟨y,⟨ha,hy⟩,hs⟩
    exact ⟨ha,hy ▸ hs⟩

theorem completeType_image (hp : B.real.Definable L p.codes) {A : Set M} {f : M → M}
    (hA : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    (hf : OverBase (L := L) p B (graphOn A f)) :
    ImaginaryBaseFamilies.CompleteType (L := L) p B (f '' A) := by
  intro S hS
  rcases hA {x | x ∈ A ∧ f x ∈ S} (preimage_definable hp hf hS) with h | h
  · exact Or.inl (by rintro _ ⟨x,hx,rfl⟩; exact (h hx).2)
  · exact Or.inr (Set.disjoint_left.mpr (by
      rintro _ ⟨x,hx,rfl⟩ hfx
      exact Set.disjoint_left.mp h hx ⟨hx,hfx⟩))

variable [Finite η]

theorem family_preimage_definable (hp : B.real.Definable L p.codes)
    {A : Set M} {f : M → M} (hf : OverBase (L := L) p B (graphOn A f))
    {C : J → Set M} (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (fun j => {x | x ∈ A ∧ f x ∈ C j}) := by
  let πC : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun a => .inl (.inl a)) Sum.inr
  let πG : Fin 2 → (η ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  have hd := OverBase.exists_block
    (OverBase.inter (hC.preimage_comp πC) (hf.preimage_comp πG) hp)
  change OverBase (L := L) p B
    (q.relationPullback (fun j => {x | x ∈ A ∧ f x ∈ C j}))
  convert hd using 1
  ext z
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      z (.inr 0) ∈ A ∧ f (z (.inr 0)) ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩)) ↔
    ∃ y : Fin 1 → M,
      (∃ hz : z ∘ Sum.inl ∈ q.codes, y 0 ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩)) ∧
      z (.inr 0) ∈ A ∧ y 0 = f (z (.inr 0))
  constructor
  · rintro ⟨hz,ha,hc⟩
    exact ⟨![f (z (.inr 0))],⟨hz,hc⟩,ha,rfl⟩
  · rintro ⟨y,⟨hz,hc⟩,ha,he⟩
    exact ⟨hz,ha,he ▸ hc⟩

end IntegrationInACVF.Section3.ImaginaryBaseImages
