module

public import IntegrationSection3.RegionFormulas

@[expose] public section

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.AtomicRegions

set_option backward.isDefEq.respectTransparency false

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂}
variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
variable [Finite η]

/-- A definable property of disjoint nonempty regions inside a complete
type is uniform across the entire family. Individual regions need not be
definable over the base. -/
theorem uniform_property (hp : B.real.Definable L p.codes)
    {A : Set M} (hA : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    {T P : Set J} {C : J → Set M}
    (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    (hP : ImaginaryBaseFamilies.Family (L := L) p B q P)
    (hC : ImaginaryBaseFamilies.Relation (L := L) p B q C)
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k)) :
    T ⊆ P ∨ Disjoint T P := by
  let S := {x | ∃ j ∈ T ∩ P, x ∈ C j}
  have hd : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S} :=
    ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp
        (ImaginaryBaseFamilies.Family.inter hp hT hP) hC)
  rcases hA S hd with hall | hnone
  · left
    intro j hj
    obtain ⟨x,hx⟩ := hne j hj
    obtain ⟨k,⟨hk,hkp⟩,hxk⟩ := hall (hsub j hj hx)
    by_cases he : j = k
    · exact he.symm ▸ hkp
    · exact (Set.disjoint_left.mp (hdis hj hk he) hx hxk).elim
  · right
    apply Set.disjoint_left.mpr
    intro j hj hjp
    obtain ⟨x,hx⟩ := hne j hj
    exact Set.disjoint_left.mp hnone (hsub j hj hx) ⟨j,⟨hj,hjp⟩,hx⟩

/-- A definable simultaneous refinement of disjoint regions inside a
complete type is trivial as soon as one refined region is nonempty.
The regions themselves need not be individually definable over the base. -/
theorem refinement_eq (hp : B.real.Definable L p.codes)
    {A : Set M} (hA : ImaginaryBaseFamilies.CompleteType (L := L) p B A)
    {T : Set J} {C D : J → Set M}
    (hT : ImaginaryBaseFamilies.Family (L := L) p B q T)
    (hD : ImaginaryBaseFamilies.Relation (L := L) p B q D)
    (hsub : ∀ j ∈ T, C j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k))
    (hDC : ∀ j ∈ T, D j ⊆ C j)
    (hne : ∃ j ∈ T, (D j).Nonempty) : ∀ j ∈ T, D j = C j := by
  let S := {x | ∃ j ∈ T, x ∈ D j}
  have hd : OverBase (L := L) p B {z : Fin 1 → M | z 0 ∈ S} :=
    ImaginaryBaseFamilies.Relation.range
      (ImaginaryBaseFamilies.Relation.restrict hp hT hD)
  have hall : A ⊆ S := by
    rcases hA S hd with hall | hnone
    · exact hall
    · obtain ⟨j,hj,x,hx⟩ := hne
      exact (Set.disjoint_left.mp hnone (hsub j hj (hDC j hj hx)) ⟨j,hj,hx⟩).elim
  intro j hj
  apply Set.Subset.antisymm (hDC j hj)
  intro x hx
  obtain ⟨k,hk,hxk⟩ := hall (hsub j hj hx)
  by_cases he : k = j
  · exact he ▸ hxk
  · exact (Set.disjoint_left.mp (hdis hj hk (fun h => he h.symm))
      hx (hDC k hk hxk)).elim

end IntegrationInACVF.Section3.AtomicRegions
