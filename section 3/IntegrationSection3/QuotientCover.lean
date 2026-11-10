module

public import IntegrationSection3.BallSupport

@[expose] public section

/-! A cover by sets lying in individual quotient classes detects infinitely
many indices on either side of a saturated cut with infinitely many classes.
This is a semantic step; actual definability and ball geometry are separate. -/

open Set

namespace IntegrationInACVF.Section3.QuotientCover

variable {X Q J : Type*}

def meets (T : Set J) (C : J → Set X) (D : Set X) : Set J :=
  {j | j ∈ T ∧ (C j ∩ D).Nonempty}

theorem image_finite_of_finite_cover (π : X → Q) {T : Set J} (hT : T.Finite)
    (C : J → Set X) (hspan : ∀ j ∈ T, ∀ x ∈ C j, ∀ y ∈ C j, π x = π y)
    {D : Set X} (hcover : ∀ x ∈ D, ∃ j ∈ T, x ∈ C j) : (π '' D).Finite := by
  have hf (j : J) (hj : j ∈ T) : (π '' C j).Subsingleton := by
    rintro q ⟨x,hx,rfl⟩ q' ⟨y,hy,rfl⟩
    exact hspan j hj x hx y hy
  have hfinite := hT.biUnion (fun j hj => (hf j hj).finite)
  apply hfinite.subset
  rintro q ⟨x,hx,rfl⟩
  obtain ⟨j,hj,hxc⟩ := hcover x hx
  exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,x,hxc,rfl⟩⟩

theorem meets_infinite (π : X → Q) {P D : Set X} (hDP : D ⊆ P)
    (hD : (π '' D).Infinite) {T : Set J} (C : J → Set X)
    (hspan : ∀ j ∈ T, ∀ x ∈ C j, ∀ y ∈ C j, π x = π y)
    (hcover : ∀ x ∈ P, ∃ j ∈ T, x ∈ C j) : (meets T C D).Infinite := by
  intro hfinite
  apply hD
  apply image_finite_of_finite_cover π hfinite C
    (fun j hj => hspan j hj.1)
  intro x hx
  obtain ⟨j,hj,hxc⟩ := hcover x (hDP hx)
  exact ⟨j,⟨hj,x,hxc,hx⟩,hxc⟩

theorem complement_infinite (π : X → Q) {P D : Set X}
    (hD : (π '' (P \ D)).Infinite) {T : Set J} (C : J → Set X)
    (hsub : ∀ j ∈ T, C j ⊆ P)
    (hspan : ∀ j ∈ T, ∀ x ∈ C j, ∀ y ∈ C j, π x = π y)
    (hsaturated : ∀ x ∈ P, ∀ y ∈ P, π x = π y → (x ∈ D ↔ y ∈ D))
    (hcover : ∀ x ∈ P, ∃ j ∈ T, x ∈ C j) : (T \ meets T C D).Infinite := by
  intro hfinite
  apply hD
  apply image_finite_of_finite_cover π hfinite C (fun j hj => hspan j hj.1)
  rintro x ⟨hxP,hxD⟩
  obtain ⟨j,hj,hxc⟩ := hcover x hxP
  refine ⟨j,⟨hj,?_⟩,hxc⟩
  rintro ⟨_,y,hyc,hyD⟩
  exact hxD ((hsaturated x hxP y (hsub j hj hyc) (hspan j hj x hxc y hyc)).mpr hyD)

end IntegrationInACVF.Section3.QuotientCover
