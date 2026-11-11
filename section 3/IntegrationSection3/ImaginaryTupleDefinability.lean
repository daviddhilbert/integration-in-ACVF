module

public import IntegrationSection3.ImaginaryParameters

@[expose] public section

/-! The full code domain and equality relation for a finite tuple of
interpreted names are definable over the unchanged real base. -/

set_option backward.isDefEq.respectTransparency false

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryTupleDefinability

universe u v w w' w'' w₁
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {η : Type w''} {θ : Type w₁}
variable [Finite η] [Finite θ] {p : Presentation M I η} {Q : Set M}

theorem isDefinable (hp : p.IsDefinable L Q) :
    (tuplePresentation p θ).IsDefinable L Q := by
  refine ⟨tupleCodes_definable hp.1 θ,?_⟩
  let π (i : θ) : η ⊕ η → (θ × η) ⊕ (θ × η) :=
    Sum.elim (fun c => .inl (i,c)) (fun c => .inr (i,c))
  have hd := Set.definable_iInter_of_finite (fun i : θ => hp.2.preimage_comp (π i))
  convert hd using 1
  ext z
  simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage]
  change (∃ hc : z ∘ Sum.inl ∈ tupleCodes p θ,
    ∃ hd : z ∘ Sum.inr ∈ tupleCodes p θ,
      (tuplePresentation p θ).decode ⟨z ∘ Sum.inl,hc⟩ =
        (tuplePresentation p θ).decode ⟨z ∘ Sum.inr,hd⟩) ↔
    ∀ i : θ, ∃ hc : (fun c => z (.inl (i,c))) ∈ p.codes,
      ∃ hd : (fun c => z (.inr (i,c))) ∈ p.codes,
        p.decode ⟨(fun c => z (.inl (i,c))),hc⟩ = p.decode ⟨(fun c => z (.inr (i,c))),hd⟩
  constructor
  · rintro ⟨hc,hd,he⟩ i
    exact ⟨hc i,hd i,congrFun he i⟩
  · intro h
    refine ⟨(fun i => (h i).choose),(fun i => (h i).choose_spec.choose),?_⟩
    funext i
    exact (h i).choose_spec.choose_spec

end IntegrationInACVF.Section3.ImaginaryTupleDefinability
