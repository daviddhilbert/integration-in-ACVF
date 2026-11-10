module

public import IntegrationSection3.ImaginaryBaseFamilies

@[expose] public section

/-! Relational preimages of an interpreted family, without assuming that
the relation is the graph of a function. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.RelationalPreimages

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def family (R : Set (M × M)) (C : J → Set M) (j : J) : Set M :=
  {x | ∃ y, (x,y) ∈ R ∧ y ∈ C j}

theorem family_definable (hp : B.real.Definable L p.codes)
    {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    {C : J → Set M} (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (family R C) := by
  let πC : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun e => .inl (.inl e)) Sum.inr
  let πR : Fin 2 → (η ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  have hd := OverBase.exists_block (OverBase.inter
    (hR.preimage_comp πR) (hC.preimage_comp πC) hp)
  change OverBase (L := L) p B (q.relationPullback (family R C))
  convert hd using 1
  ext z
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
      ∃ y, (z (.inr 0),y) ∈ R ∧ y ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩)) ↔
    (∃ y : Fin 1 → M, (z (.inr 0),y 0) ∈ R ∧
      ∃ hz : z ∘ Sum.inl ∈ q.codes, y 0 ∈ C (q.decode ⟨z ∘ Sum.inl,hz⟩))
  exact ⟨fun ⟨hz,y,hr,hc⟩ => ⟨![y],hr,hz,hc⟩,
    fun ⟨y,hr,hz,hc⟩ => ⟨hz,y 0,hr,hc⟩⟩

end IntegrationInACVF.Section3.RelationalPreimages
