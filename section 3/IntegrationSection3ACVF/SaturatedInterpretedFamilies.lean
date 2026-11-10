import IntegrationSection3.ImaginaryFamilies
import Section4.NonalgebraicTypes

/-! An infinite definable family of nonempty disjoint interpreted sets
has a nonalgebraic index over a small real base. Genuine saturation is
applied to real points; saturation of a quotient sort is not assumed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3.ImaginaryFamilies

namespace IntegrationInACVF.Section3ACVF.SaturatedInterpretedFamilies

variable {M : Type} [sM : LRV.Structure M]
variable {J η : Type} [Finite η]

noncomputable def union (U : J → Set M) (T : Set J) : Set M := {x | ∃ j ∈ T, x ∈ U j}

theorem union_definable (q : Presentation M J η) (S : Set M) {T : Set J}
    (hT : q.DefinableFamily (L := LRV) S T) {U : J → Set M}
    (hU : q.DefinableRelation (L := LRV) S U) : S.Definable₁ LRV (union U T) := by
  exact Presentation.DefinableRelation.range (Presentation.DefinableRelation.restrict hT hU)

theorem exists_nonalgebraic {κ : Cardinal} (hs : Saturated M κ) (S : Set M)
    (hsmall : Cardinal.mk S < κ) (q : Presentation M J η)
    (U : J → Set M) (hU : q.DefinableRelation (L := LRV) S U)
    (T : Set J) (hT : q.DefinableFamily (L := LRV) S T) (hInf : T.Infinite)
    (hne : ∀ j ∈ T, (U j).Nonempty) (hdis : T.Pairwise fun i j => Disjoint (U i) (U j)) :
    ∃ j ∈ T, ¬ q.Algebraic (L := LRV) S j := by
  let C : Set (Set M) := {D | ∃ F : Set J, q.DefinableFamily (L := LRV) S F ∧
    F.Finite ∧ F ⊆ T ∧ D = union U T \ union U F}
  have hC : ∀ D ∈ C, S.Definable₁ LRV D := by
    rintro D ⟨F,hF,_,_,rfl⟩
    exact (union_definable q S hT hU).sdiff (union_definable q S hF hU)
  have hFIP : ∀ (ι : Type) [Finite ι] (D : ι → C), ∃ x : M, ∀ i, x ∈ (D i).val := by
    intro ι _ D
    choose F hF hFin hSub hEq using fun i => (D i).property
    have hFinite : (⋃ i, F i).Finite := Set.finite_iUnion hFin
    have hNot : ¬ T ⊆ ⋃ i, F i := fun h => hInf (hFinite.subset h)
    obtain ⟨j,hj,hjF⟩ := Set.not_subset.mp hNot
    obtain ⟨x,hx⟩ := hne j hj
    refine ⟨x,fun i => ?_⟩
    rw [hEq i]
    refine ⟨⟨j,hj,hx⟩,?_⟩
    rintro ⟨k,hk,hxk⟩
    have hjk : j ≠ k := fun he => hjF (Set.mem_iUnion.mpr ⟨i,he.symm ▸ hk⟩)
    exact Set.disjoint_left.mp (hdis hj (hSub i hk) hjk) hx hxk
  obtain ⟨x,hx⟩ := realize_unary_definable_fip hs S hsmall C hC hFIP
  have hEmpty : q.DefinableFamily (L := LRV) S (∅ : Set J) := by
    have he : q.pullback (∅ : Set J) = (∅ : Set (η → M)) := by
      ext z
      simp [Presentation.pullback]
    change S.Definable LRV (q.pullback ∅)
    rw [he]
    exact Set.definable_empty
  have hxT : x ∈ union U T :=
    (hx (union U T \ union U ∅) ⟨∅,hEmpty,Set.finite_empty,Set.empty_subset T,rfl⟩).1
  obtain ⟨j,hj,hxj⟩ := hxT
  refine ⟨j,hj,?_⟩
  rintro ⟨F,hF,hFin,hjF⟩
  have hFT := Presentation.DefinableFamily.inter hF hT
  have hAvoid := hx (union U T \ union U (F ∩ T))
    ⟨F ∩ T,hFT,hFin.inter_of_left T,Set.inter_subset_right,rfl⟩
  exact hAvoid.2 ⟨j,⟨hjF,hj⟩,hxj⟩

end IntegrationInACVF.Section3ACVF.SaturatedInterpretedFamilies
