module

public import IntegrationSection3.BallSupport

@[expose] public section

/-! A finite ball-supported cover gives a finite hitting set for every
ball family whose members are contained in no one cover piece. -/

open Set Classical

namespace IntegrationInACVF.Section3.FiniteSupportHitting

variable {X J : Type*}

theorem finite_hitting_set (balls : Set (Set X)) (hLam : IsLaminar balls)
    (hNonempty : ∀ b ∈ balls, b.Nonempty)
    (T : Set J) (U : J → Set X) (hU : ∀ j ∈ T, U j ∈ balls)
    (C : Finset (Set X)) (hC : ∀ D ∈ C, HasFiniteBallSupport balls D)
    (hCover : ∀ j ∈ T, ∀ x ∈ U j, ∃ D ∈ C, x ∈ D)
    (hNot : ∀ j ∈ T, ∀ D ∈ C, ¬ U j ⊆ D) :
    ∃ F : Finset X, ∀ j ∈ T, ∃ x ∈ F, x ∈ U j := by
  classical
  choose G hG hSupport using fun D : C => hC D.val D.property
  let H := Finset.univ.biUnion (fun D : C => G D)
  have hH (b : Set X) (hb : b ∈ H) : b ∈ balls := by
    obtain ⟨D,_,hb⟩ := Finset.mem_biUnion.mp hb
    exact hG D b hb
  choose point hPoint using fun b : H => hNonempty b.val (hH b.val b.property)
  let F := Finset.univ.image point
  refine ⟨F,?_⟩
  intro j hj
  obtain ⟨x,hx⟩ := hNonempty (U j) (hU j hj)
  obtain ⟨D,hD,hxD⟩ := hCover j hj x hx
  obtain ⟨y,hy,hyD⟩ := Set.not_subset.mp (hNot j hj D hD)
  have hSplit : Splits D (U j) := ⟨x,hx,hxD,y,hy,hyD⟩
  obtain ⟨b,hb,hbSplit⟩ := splits_support (hSupport ⟨D,hD⟩) hSplit
  have hbH : b ∈ H := Finset.mem_biUnion.mpr ⟨⟨D,hD⟩,Finset.mem_univ _,hb⟩
  have hSub := hLam.subset_of_splits (hG ⟨D,hD⟩ b hb) (hU j hj) hbSplit
  exact ⟨point ⟨b,hbH⟩,Finset.mem_image.mpr ⟨⟨b,hbH⟩,Finset.mem_univ _,rfl⟩,
    hSub (hPoint ⟨b,hbH⟩)⟩

end IntegrationInACVF.Section3.FiniteSupportHitting
