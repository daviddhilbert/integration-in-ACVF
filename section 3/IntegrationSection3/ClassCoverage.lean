module

public import IntegrationSection3.SupportFormulas

@[expose] public section

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ClassCoverage

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {B : Base M I}

def wholeClass (R : Set (M × M)) (A : Set M) : Set M :=
  {x | ∀ y, (x,y) ∈ R → y ∈ A}

theorem wholeClass_definable (hp : B.real.Definable L p.codes)
    {R : Set (M × M)} {A : Set M}
    (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A})
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ wholeClass R A} := by
  have hr := hR.preimage_comp (![.inl 0,.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have ha := hA.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
  have hall := OverBase.forall_block (SupportFormulas.imp_definable hp hr ha) hp
  convert hall using 1
  ext z
  change (∀ y, (z 0,y) ∈ R → y ∈ A) ↔
    ∀ t : Fin 1 → M, (z 0,t 0) ∈ R → t 0 ∈ A
  exact ⟨fun h t => h (t 0),fun h y => h ![y]⟩

theorem complete_type_cover (hp : B.real.Definable L p.codes)
    {R : Set (M × M)} {A : Set M}
    (hA : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    (hw : ∃ x ∈ A, x ∈ wholeClass R A) : A ⊆ wholeClass R A := by
  rcases hAtomic (wholeClass R A) (wholeClass_definable hp hA hR) with h | h
  · exact h
  · obtain ⟨x,hx,hw⟩ := hw
    exact (Set.disjoint_left.mp h hx hw).elim

end IntegrationInACVF.Section3.ClassCoverage
