module

public import IntegrationSection3.DefinablePartitions

@[expose] public section

/-! A finite Boolean partition simultaneously refines every cover in a
finite family. The family may be empty. Definability retains the original
interpreted base. -/

open Set FirstOrder
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters
open IntegrationInACVF.Section3.DefinablePartitions

namespace IntegrationInACVF.Section3.SimultaneousPartitions

variable {X : Type*}

theorem cell_subordinate_subfamily {A : Set X} {F T H : Finset (Set X)}
    (hHF : H ⊆ F) (hCov : ∀ x ∈ A, ∃ U ∈ H, x ∈ U)
    (hne : (cell A F T).Nonempty) : ∃ U ∈ H, cell A F T ⊆ U := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨U,hUH,hxU⟩ := hCov x hx.1
  exact ⟨U,hUH,fun y hy => (hy.2 U (hHF hUH)).mpr ((hx.2 U (hHF hUH)).mp hxU)⟩

universe u v w w' w'' w₁ w₂
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]
variable {I : Type w'} {κ : Type w''} {α : Type w₁} [Finite α]
variable {p : Presentation M I κ} {B : Base M I} {θ : Type w₂} [Finite θ]

theorem exists_partition (hp : B.real.Definable L p.codes)
    {A : Set (α → M)} (hA : OverBase (L := L) p B A)
    (covers : θ → Finset (Set (α → M)))
    (hDef : ∀ t U, U ∈ covers t → OverBase (L := L) p B U)
    (hCov : ∀ t x, x ∈ A → ∃ U ∈ covers t, x ∈ U) :
    ∃ G : Finset (Set (α → M)),
      (∀ C ∈ G, C.Nonempty ∧ C ⊆ A ∧ OverBase (L := L) p B C ∧
        ∀ t, ∃ U ∈ covers t, C ⊆ U) ∧
      (G : Set (Set (α → M))).Pairwise Disjoint ∧ A = {x | ∃ C ∈ G, x ∈ C} := by
  classical
  letI := Fintype.ofFinite θ
  let F := Finset.univ.biUnion covers
  have hSub (t : θ) : covers t ⊆ F := fun U hU => Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ t,hU⟩
  have hF (U : Set (α → M)) (hU : U ∈ F) : OverBase (L := L) p B U := by
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hU
    exact hDef t U ht
  let G := (F.powerset.image (cell A F)).filter Set.Nonempty
  have hMem (C : Set (α → M)) : C ∈ G ↔ ∃ T ⊆ F, cell A F T = C ∧ C.Nonempty := by
    simp only [G,Finset.mem_filter,Finset.mem_image,Finset.mem_powerset]
    exact ⟨fun ⟨⟨T,hT,he⟩,hne⟩ => ⟨T,hT,he,hne⟩,fun ⟨T,hT,he,hne⟩ => ⟨⟨T,hT,he⟩,hne⟩⟩
  refine ⟨G,?_,?_,?_⟩
  · intro C hC
    obtain ⟨T,_,rfl,hne⟩ := (hMem C).mp hC
    exact ⟨hne,fun _ hx => hx.1,cell_definable hp hA F T hF,
      fun t => cell_subordinate_subfamily (hSub t) (hCov t) hne⟩
  · intro C hC D hD hCD
    obtain ⟨T,hT,rfl,_⟩ := (hMem C).mp hC
    obtain ⟨V,hV,rfl,_⟩ := (hMem D).mp hD
    exact cells_disjoint hT hV (fun he => hCD (he ▸ rfl))
  · ext x
    constructor
    · intro hx
      let T := F.filter fun U => x ∈ U
      have hxC : x ∈ cell A F T := by
        refine ⟨hx,fun U hU => ?_⟩
        exact ⟨fun hxU => Finset.mem_filter.mpr ⟨hU,hxU⟩,fun ht => (Finset.mem_filter.mp ht).2⟩
      exact ⟨cell A F T,(hMem _).mpr ⟨T,Finset.filter_subset _ _,rfl,x,hxC⟩,hxC⟩
    · rintro ⟨C,hC,hxC⟩
      obtain ⟨T,_,rfl,_⟩ := (hMem C).mp hC
      exact hxC.1

end IntegrationInACVF.Section3.SimultaneousPartitions
