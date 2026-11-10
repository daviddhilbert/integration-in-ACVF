module

public import IntegrationSection3.ImaginaryBaseImages
public import Mathlib.Data.Set.Function

@[expose] public section

/-! The inverse of an injective map on a definable domain has precisely
the transposed graph over the unchanged interpreted parameter base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.PartialInverse

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [Nonempty M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {B : Base M I}

theorem graph_eq {A : Set M} {f : M → M} (hinj : Set.InjOn f A) :
    ImaginaryBaseImages.graphOn (f '' A) (Function.invFunOn f A) =
      (fun z : Fin 2 → M => z ∘ ![1,0]) ⁻¹' ImaginaryBaseImages.graphOn A f := by
  ext z
  change (z 0 ∈ f '' A ∧ z 1 = Function.invFunOn f A (z 0)) ↔
    (z 1 ∈ A ∧ z 0 = f (z 1))
  constructor
  · rintro ⟨hx,hy⟩
    have hm := Function.invFunOn_mem hx
    have he := Function.invFunOn_eq hx
    exact ⟨hy.symm ▸ hm,by rw [hy,he]⟩
  · rintro ⟨hy,he⟩
    refine ⟨⟨z 1,hy,he.symm⟩,?_⟩
    rw [he,hinj.leftInvOn_invFunOn hy]

theorem graph_definable {A : Set M} {f : M → M} (hinj : Set.InjOn f A)
    (hf : OverBase (L := L) p B (ImaginaryBaseImages.graphOn A f)) :
    OverBase (L := L) p B
      (ImaginaryBaseImages.graphOn (f '' A) (Function.invFunOn f A)) := by
  rw [graph_eq hinj]
  exact hf.preimage_comp ![1,0]

end IntegrationInACVF.Section3.PartialInverse
