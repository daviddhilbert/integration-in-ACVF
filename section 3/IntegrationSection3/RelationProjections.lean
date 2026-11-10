module

public import IntegrationSection3.ImaginaryBaseFamilies

@[expose] public section

/-! Projection surjectivity for a nonempty relation over the full
interpreted parameter base. Nonemptiness is the approved 3.11 correction. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.RelationProjections

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {B : Base M I}

theorem domain_definable {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    OverBase (L := L) p B {z : Fin 1 → M | ∃ y, (z 0,y) ∈ R} := by
  have hd := OverBase.exists_block (hR.preimage_comp
    (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  convert hd using 1
  ext z
  exact ⟨fun ⟨y,hy⟩ => ⟨![y],hy⟩,fun ⟨y,hy⟩ => ⟨y 0,hy⟩⟩

theorem range_definable {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    OverBase (L := L) p B {z : Fin 1 → M | ∃ x, (x,z 0) ∈ R} := by
  have hd := OverBase.exists_block (hR.preimage_comp
    (![Sum.inr 0,Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  convert hd using 1
  ext z
  exact ⟨fun ⟨x,hx⟩ => ⟨![x],hx⟩,fun ⟨x,hx⟩ => ⟨x 0,hx⟩⟩

theorem surjective {P Q : Set M}
    (hP : ImaginaryBaseFamilies.CompleteType (L := L) p B P)
    (hQ : ImaginaryBaseFamilies.CompleteType (L := L) p B Q)
    {R : Set (M × M)}
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hsub : R ⊆ P ×ˢ Q) (hne : R.Nonempty) :
    (∀ x ∈ P, ∃ y ∈ Q, (x,y) ∈ R) ∧ (∀ y ∈ Q, ∃ x ∈ P, (x,y) ∈ R) := by
  obtain ⟨⟨x0,y0⟩,h0⟩ := hne
  have hPx : x0 ∈ P := (hsub h0).1
  have hQy : y0 ∈ Q := (hsub h0).2
  constructor
  · have hall : P ⊆ {x | ∃ y, (x,y) ∈ R} := by
      rcases hP {x | ∃ y, (x,y) ∈ R} (domain_definable hR) with hall | hnone
      · exact hall
      · exact (Set.disjoint_left.mp hnone hPx ⟨y0,h0⟩).elim
    intro x hx
    obtain ⟨y,hy⟩ := hall hx
    exact ⟨y,(hsub hy).2,hy⟩
  · have hall : Q ⊆ {y | ∃ x, (x,y) ∈ R} := by
      rcases hQ {y | ∃ x, (x,y) ∈ R} (range_definable hR) with hall | hnone
      · exact hall
      · exact (Set.disjoint_left.mp hnone hQy ⟨x0,h0⟩).elim
    intro y hy
    obtain ⟨x,hx⟩ := hall hy
    exact ⟨x,(hsub hx).1,hx⟩

end IntegrationInACVF.Section3.RelationProjections
