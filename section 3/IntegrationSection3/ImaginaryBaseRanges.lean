module

public import IntegrationSection3.ImaginaryBaseFamilies
public import IntegrationSection3.InterpretedRanges

@[expose] public section

/-! Full-code ranges and subsingleton fibres over the original interpreted base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.ImaginaryBaseFamilies

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

theorem rangeFamily_definable (hp : B.real.Definable L p.codes)
    (hq : B.real.Definable L q.codes)
    {U : J → Set M} (hU : Relation (L := L) p B q U)
    {D : Set M} (hD : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ D})
    {R : Set (M × M)} (hR : OverBase (L := L) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}) :
    Family (L := L) p B q (rangeFamily U D R) := by
  let πU : η ⊕ Fin 1 → (η ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πR : Fin 2 → (η ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  have hu := OverBase.preimage_comp hU πU
  have hr := OverBase.preimage_comp hR πR
  have hi : OverBase (L := L) p B {z : (η ⊕ Fin 1) ⊕ Fin 1 → M |
      z ∘ πU ∈ q.relationPullback U ↔ (z (.inl (.inr 0)),z (.inr 0)) ∈ R} := by
    convert OverBase.compl
      (OverBase.inter
        (OverBase.compl (OverBase.inter hu hr hp) hp)
        (OverBase.compl (OverBase.inter (OverBase.compl hu hp) (OverBase.compl hr hp) hp) hp) hp) hp using 1
    ext z
    change (_ ↔ _) ↔ ¬ (¬ (_ ∧ _) ∧ ¬ (¬ _ ∧ ¬ _))
    tauto
  have hall := OverBase.forall_block hi hp
  have hex := OverBase.exists_block
    (OverBase.inter (hD.preimage_comp (Sum.inr : Fin 1 → η ⊕ Fin 1)) hall hp)
  change OverBase (L := L) p B (q.pullback (rangeFamily U D R))
  convert OverBase.inter (OverBase.of_real hq) hex hp using 1
  ext c
  constructor
  · rintro ⟨hc,a,ha,he⟩
    refine ⟨hc,![a],ha,?_⟩
    intro x
    change (∃ h : c ∈ q.codes, x 0 ∈ U (q.decode ⟨c,h⟩)) ↔ (a,x 0) ∈ R
    constructor
    · rintro ⟨_,hx⟩
      exact (Set.ext_iff.mp he (x 0)).mp hx
    · intro hx
      exact ⟨hc,(Set.ext_iff.mp he (x 0)).mpr hx⟩
  · rintro ⟨hc,a,ha,he⟩
    refine ⟨hc,a 0,ha,Set.ext fun x => ?_⟩
    have hx := he ![x]
    change (∃ h : c ∈ q.codes, x ∈ U (q.decode ⟨c,h⟩)) ↔ (a 0,x) ∈ R at hx
    exact ⟨fun h => hx.mp ⟨hc,h⟩,fun h => (hx.mpr h).choose_spec⟩

omit [Finite η] in
theorem atomicWith_of_subsingleton {U : J → Set M}
    (hU : Relation (L := L) p B q U) (i : J) (hi : (U i).Subsingleton) :
    AtomicWith (L := L) p B q i (U i) := by
  classical
  refine ⟨⟨U,hU,rfl⟩,fun S _ => ?_⟩
  by_cases h : (U i ∩ S).Nonempty
  · obtain ⟨x,hxi,hxS⟩ := h
    exact Or.inl (fun y hy => (hi hy hxi).symm ▸ hxS)
  · exact Or.inr (Set.disjoint_left.mpr fun x hxi hxS => h ⟨x,hxi,hxS⟩)

end IntegrationInACVF.Section3.ImaginaryBaseFamilies
