module

public import IntegrationSection3.ImaginaryBaseFamilies
public import IntegrationSection3.SupportFormulas

@[expose] public section

/-! Equality of an interpreted point set with a real-indexed relation
fibre, and composition through that interpreted name. All real codes are
retained; the formulas do not select representatives. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.FibreEqualityFormulas

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

def equalFibres (U : J → Set M) (D : Set M) (R : Set (M × M)) : J → Set M :=
  fun j => {y | y ∈ D ∧ ∀ x, (x ∈ U j ↔ (y,x) ∈ R)}

theorem equalFibres_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes)
    {U : J → Set M} (hU : ImaginaryBaseFamilies.Relation (L := L) p B q U)
    {D : Set M} (hD : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ D})
    {R : Set (M × M)} (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    ImaginaryBaseFamilies.Relation (L := L) p B q (equalFibres U D R) := by
  let πU : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πR : Fin 2 → (η ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  have hu := hU.preimage_comp πU
  have hr := hR.preimage_comp πR
  have hall := OverBase.forall_block (SupportFormulas.iff_definable hp hu hr) hp
  have hy := hD.preimage_comp (Sum.inr : Fin 1 → η ⊕ Fin 1)
  have hc := (OverBase.of_real (p := p) (B := B) hq).preimage_comp
    (Sum.inl : η → η ⊕ Fin 1)
  change OverBase (L := L) p B (q.relationPullback (equalFibres U D R))
  convert OverBase.inter hc (OverBase.inter hy hall hp) hp using 1
  ext z
  change (∃ hz : z ∘ Sum.inl ∈ q.codes,
    z (.inr 0) ∈ D ∧ ∀ x, (x ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩) ↔ (z (.inr 0),x) ∈ R)) ↔
    (z ∘ Sum.inl ∈ q.codes ∧ z (.inr 0) ∈ D ∧ ∀ x : Fin 1 → M,
      (∃ hz : z ∘ Sum.inl ∈ q.codes, x 0 ∈ U (q.decode ⟨z ∘ Sum.inl,hz⟩)) ↔
        (z (.inr 0),x 0) ∈ R)
  constructor
  · rintro ⟨hz,hy,he⟩
    refine ⟨hz,hy,fun x => ?_⟩
    exact ⟨fun ⟨_,hx⟩ => (he (x 0)).mp hx,fun hx => ⟨hz,(he (x 0)).mpr hx⟩⟩
  · rintro ⟨hz,hy,he⟩
    refine ⟨hz,hy,fun x => ?_⟩
    exact ⟨fun hx => (he ![x]).mp ⟨hz,hx⟩,fun hx => ((he ![x]).mpr hx).choose_spec⟩

theorem compose_definable (hp : B.real.Definable L p.codes)
    {A C : J → Set M}
    (hA : ImaginaryBaseFamilies.Relation (L := L) p B q A)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C) :
    OverBase (L := L) p B {z : Fin 2 → M | ∃ j, z 0 ∈ A j ∧ z 1 ∈ C j} := by
  have hx := hA.preimage_comp (Sum.map id (fun _ : Fin 1 => (0 : Fin 2)))
  have hy := hC.preimage_comp (Sum.map id (fun _ : Fin 1 => (1 : Fin 2)))
  have hpair := OverBase.inter hx hy hp
  have hd := OverBase.exists_block (hpair.preimage_comp (Sum.swap : η ⊕ Fin 2 → Fin 2 ⊕ η))
  convert hd using 1
  ext z
  change (∃ j, z 0 ∈ A j ∧ z 1 ∈ C j) ↔
    ∃ c : η → M, (∃ hc : c ∈ q.codes, z 0 ∈ A (q.decode ⟨c,hc⟩)) ∧
      ∃ hc : c ∈ q.codes, z 1 ∈ C (q.decode ⟨c,hc⟩)
  constructor
  · rintro ⟨j,hx,hy⟩
    obtain ⟨c,rfl⟩ := q.onto j
    exact ⟨c.val,⟨c.property,hx⟩,c.property,hy⟩
  · rintro ⟨c,⟨hc,hx⟩,⟨_,hy⟩⟩
    exact ⟨q.decode ⟨c,hc⟩,hx,hy⟩

end IntegrationInACVF.Section3.FibreEqualityFormulas
