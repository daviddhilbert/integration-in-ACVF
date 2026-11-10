module

public import IntegrationSection3.ImaginaryFamilies

@[expose] public section

/-!
# Definable ranges of families of interpreted point sets

An interpreted object belongs to the range precisely when its underlying
point set equals one of the definable fibres. Equality is tested by a real
universal quantifier. This retains all codes and the original parameter base.
-/

open Set FirstOrder

namespace IntegrationInACVF.Section3.ImaginaryFamilies

set_option backward.isDefEq.respectTransparency false

universe u v w w' w''
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''}
variable {p : Presentation M I κ} {Q : Set M}

def rangeFamily (U : I → Set M) (D : Set M) (R : Set (M × M)) : Set I :=
  {i | ∃ a ∈ D, U i = DefinableFamilies.fibre R a}

theorem rangeFamily_definable (hp : p.IsDefinable L Q)
    {U : I → Set M} (hU : p.DefinableRelation (L := L) Q U)
    {D : Set M} (hD : Q.Definable₁ L D)
    {R : Set (M × M)} (hR : Q.Definable₂ L R) :
    p.DefinableFamily (L := L) Q (rangeFamily U D R) := by
  let πU : κ ⊕ Fin 1 → (κ ⊕ Fin 1) ⊕ Fin 1 :=
    Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let πR : Fin 2 → (κ ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  have hu := hU.preimage_comp πU
  have hr := hR.preimage_comp πR
  have hiff : Q.Definable L {z : (κ ⊕ Fin 1) ⊕ Fin 1 → M |
      z ∘ πU ∈ p.relationPullback U ↔ (z (.inl (.inr 0)),z (.inr 0)) ∈ R} := by
    convert (hu.himp hr).inter (hr.himp hu) using 1
    ext z
    change (_ ↔ _) ↔ ((_ → _) ∧ (_ → _))
    exact iff_iff_implies_and_implies
  have hall := hiff.forall_of_finite
  have hex := ((hD.preimage_comp (Sum.inr : Fin 1 → κ ⊕ Fin 1)).inter hall).exists_of_finite
  change Q.Definable L (p.pullback (rangeFamily U D R))
  convert hp.1.inter hex using 1
  ext q
  constructor
  · rintro ⟨hq,a,ha,he⟩
    refine ⟨hq,![a],ha,?_⟩
    intro x
    change (∃ h : q ∈ p.codes, x 0 ∈ U (p.decode ⟨q,h⟩)) ↔ (a,x 0) ∈ R
    constructor
    · rintro ⟨_,hx⟩
      exact (Set.ext_iff.mp he (x 0)).mp hx
    · intro hx
      exact ⟨hq,(Set.ext_iff.mp he (x 0)).mpr hx⟩
  · rintro ⟨hq,a,ha,he⟩
    refine ⟨hq,a 0,ha,Set.ext fun x => ?_⟩
    have hx := he ![x]
    change (∃ h : q ∈ p.codes, x ∈ U (p.decode ⟨q,h⟩)) ↔ (a 0,x) ∈ R at hx
    exact ⟨fun h => hx.mp ⟨hq,h⟩,fun h => (hx.mpr h).choose_spec⟩

/-- A definable interpreted fibre containing at most one point is atomic
over its imaginary name, including the empty-set convention of Definition 3.1. -/
theorem atomicWith_of_subsingleton {U : I → Set M}
    (hU : p.DefinableRelation (L := L) Q U) (i : I) (hi : (U i).Subsingleton) :
    p.AtomicWith (L := L) Q i (U i) := by
  classical
  refine ⟨⟨U,hU,rfl⟩,fun S _ => ?_⟩
  by_cases h : (U i ∩ S).Nonempty
  · obtain ⟨x,hxi,hxS⟩ := h
    exact Or.inl (fun y hy => (hi hy hxi).symm ▸ hxS)
  · exact Or.inr (Set.disjoint_left.mpr fun x hxi hxS => h ⟨x,hxi,hxS⟩)

end IntegrationInACVF.Section3.ImaginaryFamilies
