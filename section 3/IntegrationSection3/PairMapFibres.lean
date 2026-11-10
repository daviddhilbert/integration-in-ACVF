module

public import IntegrationSection3.ImaginaryBaseImages

@[expose] public section

/-! Full interpreted-base formulas for the pair of difference values of
points and their images. The total extension of a partial map is unused
outside its stated domain. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.PairMapFibres

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {B : Base M I}

def family (A : Set M) (f : M → M) (d : M → M → M) (x : M) : Set (Fin 2 → M) :=
  {t | ∃ y ∈ A, t 0 = d y x ∧ t 1 = d (f y) (f x)}

def graph (A : Set M) (f : M → M) (d : M → M → M) : Set (Fin 3 → M) :=
  {z | z 0 ∈ A ∧ ![z 1,z 2] ∈ family A f d (z 0)}

theorem graph_definable (hp : B.real.Definable L p.codes)
    {A : Set M} {f : M → M} {d : M → M → M}
    (hf : OverBase (L := L) p B (ImaginaryBaseImages.graphOn A f))
    (hd : OverBase (L := L) p B {z : Fin 3 → M | z 2 = d (z 0) (z 1)}) :
    OverBase (L := L) p B (graph A f d) := by
  let X : Fin 2 → Fin 3 ⊕ Fin 3 := ![.inl 0,.inr 1]
  let Y : Fin 2 → Fin 3 ⊕ Fin 3 := ![.inr 0,.inr 2]
  let D : Fin 3 → Fin 3 ⊕ Fin 3 := ![.inr 0,.inl 0,.inl 1]
  let E : Fin 3 → Fin 3 ⊕ Fin 3 := ![.inr 2,.inr 1,.inl 2]
  have h := OverBase.exists_block
    (OverBase.inter (hf.preimage_comp X)
      (OverBase.inter (hf.preimage_comp Y)
        (OverBase.inter (hd.preimage_comp D) (hd.preimage_comp E) hp) hp) hp)
  convert h using 1
  ext z
  change (z 0 ∈ A ∧ ∃ y ∈ A, z 1 = d y (z 0) ∧ z 2 = d (f y) (f (z 0))) ↔
    ∃ w : Fin 3 → M, (z 0 ∈ A ∧ w 1 = f (z 0)) ∧
      (w 0 ∈ A ∧ w 2 = f (w 0)) ∧ z 1 = d (w 0) (z 0) ∧ z 2 = d (w 2) (w 1)
  constructor
  · rintro ⟨hx,y,hy,ht,hs⟩
    exact ⟨![y,f (z 0),f y],⟨hx,rfl⟩,⟨hy,rfl⟩,ht,hs⟩
  · rintro ⟨w,⟨hx,hfx⟩,⟨hy,hfy⟩,ht,hs⟩
    exact ⟨hx,w 0,hy,ht,by simpa only [hfx,hfy] using hs⟩

end IntegrationInACVF.Section3.PairMapFibres
