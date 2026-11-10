module

public import IntegrationSection3.ImaginaryParameters
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-! The finite Boolean refinement step for the partitions in 3.19 and
3.21. This does not supply their local open-to-open geometry or compactness
argument. Every resulting cell is definable over the unchanged base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3.DefinablePartitions

variable {X : Type*}

def cell (A : Set X) (F T : Finset (Set X)) : Set X :=
  {x | x ∈ A ∧ ∀ S ∈ F, x ∈ S ↔ S ∈ T}

theorem cell_subordinate {A : Set X} {F T : Finset (Set X)}
    (hcover : ∀ x ∈ A, ∃ S ∈ F, x ∈ S) (hne : (cell A F T).Nonempty) :
    ∃ S ∈ F, cell A F T ⊆ S := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨S,hS,hxS⟩ := hcover x hx.1
  exact ⟨S,hS,fun y hy => (hy.2 S hS).mpr ((hx.2 S hS).mp hxS)⟩

theorem cells_disjoint {A : Set X} {F T V : Finset (Set X)}
    (hT : T ⊆ F) (hV : V ⊆ F) (hne : T ≠ V) :
    Disjoint (cell A F T) (cell A F V) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hne
  apply Finset.ext
  intro S
  by_cases hS : S ∈ F
  · exact (hx.2 S hS).symm.trans (hy.2 S hS)
  · exact iff_of_false (fun h => hS (hT h)) (fun h => hS (hV h))

universe u v w w' w'' w₁
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {α : Type w₁} [Finite α]
variable {p : Presentation M I κ} {B : Base M I}

theorem cell_definable (hp : B.real.Definable L p.codes)
    {A : Set (α → M)} (hA : OverBase (L := L) p B A)
    (F T : Finset (Set (α → M)))
    (hF : ∀ S ∈ F, OverBase (L := L) p B S) :
    OverBase (L := L) p B (cell A F T) := by
  classical
  let P : F → Set (α → M) := fun S => if S.val ∈ T then S.val else S.valᶜ
  have hP : ∀ S : F, OverBase (L := L) p B (P S) := by
    intro S
    dsimp only [P]
    split
    · exact hF S.val S.property
    · exact OverBase.compl (hF S.val S.property) hp
  have hd := OverBase.inter hA (OverBase.forall_finite hP hp) hp
  convert hd using 1
  ext x
  change (x ∈ A ∧ ∀ S ∈ F, x ∈ S ↔ S ∈ T) ↔
    (x ∈ A ∧ ∀ S : F, x ∈ P S)
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hx S
    dsimp only [P]
    by_cases h : S.val ∈ T
    · rw [ite_eq_left h]
      exact (hx S.val S.property).mpr h
    · rw [ite_eq_right h]
      exact fun hxS => h ((hx S.val S.property).mp hxS)
  · intro hx S hS
    have hs := hx ⟨S,hS⟩
    dsimp only [P] at hs
    by_cases hST : S ∈ T
    · rw [ite_eq_left hST] at hs
      exact iff_of_true hs hST
    · rw [ite_eq_right hST] at hs
      exact iff_of_false hs hST

/-- A finite definable cover has a finite definable disjoint refinement.
Every nonempty cell lies in one member of the original cover. -/
theorem exists_partition (hp : B.real.Definable L p.codes)
    {A : Set (α → M)} (hA : OverBase (L := L) p B A)
    (F : Finset (Set (α → M)))
    (hF : ∀ S ∈ F, OverBase (L := L) p B S)
    (hcover : ∀ x ∈ A, ∃ S ∈ F, x ∈ S) :
    ∃ G : Finset (Set (α → M)),
      (∀ C ∈ G, C.Nonempty ∧ C ⊆ A ∧ OverBase (L := L) p B C ∧ ∃ S ∈ F, C ⊆ S) ∧
      (G : Set (Set (α → M))).Pairwise Disjoint ∧
      A = {x | ∃ C ∈ G, x ∈ C} := by
  classical
  let G := (F.powerset.image (cell A F)).filter Set.Nonempty
  have hmem (C : Set (α → M)) : C ∈ G ↔
      ∃ T ⊆ F, cell A F T = C ∧ C.Nonempty := by
    simp only [G,Finset.mem_filter,Finset.mem_image,Finset.mem_powerset]
    constructor
    · rintro ⟨⟨T,hT,hTC⟩,hne⟩
      exact ⟨T,hT,hTC,hne⟩
    · rintro ⟨T,hT,hTC,hne⟩
      exact ⟨⟨T,hT,hTC⟩,hne⟩
  refine ⟨G,?_,?_,?_⟩
  · intro C hC
    obtain ⟨T,_,rfl,hne⟩ := (hmem C).mp hC
    exact ⟨hne,fun _ h => h.1,cell_definable hp hA F T hF,cell_subordinate hcover hne⟩
  · intro C hC D hD hCD
    obtain ⟨T,hT,rfl,_⟩ := (hmem C).mp hC
    obtain ⟨V,hV,rfl,_⟩ := (hmem D).mp hD
    apply cells_disjoint hT hV
    exact fun he => hCD (he ▸ rfl)
  · ext x
    constructor
    · intro hx
      let T := F.filter fun S => x ∈ S
      have hxC : x ∈ cell A F T := by
        refine ⟨hx,fun S hS => ?_⟩
        exact ⟨fun h => Finset.mem_filter.mpr ⟨hS,h⟩,
          fun h => (Finset.mem_filter.mp h).2⟩
      exact ⟨cell A F T,(hmem _).mpr
        ⟨T,Finset.filter_subset _ _,rfl,x,hxC⟩,hxC⟩
    · rintro ⟨C,hC,hxC⟩
      obtain ⟨T,_,rfl,_⟩ := (hmem C).mp hC
      exact hxC.1

end IntegrationInACVF.Section3.DefinablePartitions
