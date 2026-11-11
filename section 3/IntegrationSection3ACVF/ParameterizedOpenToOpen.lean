import IntegrationSection3ACVF.ParameterizedOpenImages
import IntegrationSection3ACVF.MaximalOpenClasses

/-! A first-order uniform open-to-open test on each cell. The backward
test uses the swapped restricted graph, so no arbitrary total inverse or
extra inverse parameters occur. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.ParameterizedOpenToOpen

open UnaryRelationFamilies ParameterizedOpenImages

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def twoWay (G : Set (σ ⊕ Fin 2 → M)) (C : Set (σ ⊕ Fin 1 → M)) : Set (σ → M) :=
  good G C ∩ good (swap (restrict G C)) (UnaryRelationFamilies.image G C)

theorem twoWay_definable [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {C : Set (σ ⊕ Fin 1 → M)} (hC : FullBaseAtomicity.OverBase B C) :
    FullBaseAtomicity.OverBase B (twoWay G C) :=
  FullBaseAtomicity.OverBase.inter (good_definable B hG hC)
    (good_definable B (swap_definable B (restrict_definable B hG hC))
      (image_definable B hG hC))

theorem relImage_eq {G : Set (σ ⊕ Fin 2 → M)} (p : σ → M)
    (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x)
    {D : Set M} (hDA : D ⊆ A) : relImage G p D = f '' D := by
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,((hG x y).mp hxy).2.symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(hG x (f x)).mpr ⟨hDA hx,rfl⟩⟩

theorem image_fibre_eq {G : Set (σ ⊕ Fin 2 → M)} {C : Set (σ ⊕ Fin 1 → M)}
    (p : σ → M) (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x)
    (hCA : fibre C p ⊆ A) : fibre (UnaryRelationFamilies.image G C) p = f '' fibre C p := by
  ext y
  change (∃ x, pair p x y ∈ G ∧ Sum.elim p ![x] ∈ C) ↔ y ∈ f '' fibre C p
  constructor
  · rintro ⟨x,hxy,hx⟩
    exact ⟨x,hx,((hG x y).mp hxy).2.symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,(hG x (f x)).mpr ⟨hCA hx,rfl⟩,hx⟩

theorem reverse_image_eq {G : Set (σ ⊕ Fin 2 → M)} {C : Set (σ ⊕ Fin 1 → M)}
    (p : σ → M) (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x)
    (hCA : fibre C p ⊆ A) (E : Set M) :
    relImage (swap (restrict G C)) p E = {x | x ∈ fibre C p ∧ f x ∈ E} := by
  ext x
  change (∃ y ∈ E, pair p y x ∈ swap (restrict G C)) ↔ _
  have he (y : M) : pair p y x ∈ swap (restrict G C) ↔
      pair p x y ∈ G ∧ Sum.elim p ![x] ∈ C := Iff.rfl
  simp_rw [he,hG]
  constructor
  · rintro ⟨y,hy,⟨_,rfl⟩,hx⟩
    exact ⟨hx,hy⟩
  · rintro ⟨hx,hy⟩
    exact ⟨f x,hy,⟨hCA hx,rfl⟩,hx⟩

theorem twoWay_iff {G : Set (σ ⊕ Fin 2 → M)} {C : Set (σ ⊕ Fin 1 → M)}
    (p : σ → M) (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x)
    (hCA : fibre C p ⊆ A) (hinj : Set.InjOn f A) :
    p ∈ twoWay G C ↔ MaximalOpenClasses.OpenToOpen (fibre C p) f := by
  have hImage := image_fibre_eq p A f hG hCA
  constructor
  · rintro ⟨hF,hR⟩ D hDC
    have hf := (good_iff G C p).mp hF
    have hr := (good_iff (swap (restrict G C)) (UnaryRelationFamilies.image G C) p).mp hR
    constructor
    · intro ho
      have he := relImage_eq p A f hG (hDC.trans hCA)
      exact he ▸ hf D hDC ho
    · intro ho
      have hsub : f '' D ⊆ fibre (UnaryRelationFamilies.image G C) p := by
        rw [hImage]
        exact Set.image_mono hDC
      have he : relImage (swap (restrict G C)) p (f '' D) = D := by
        rw [reverse_image_eq p A f hG hCA]
        ext x
        constructor
        · rintro ⟨hx,⟨y,hy,he⟩⟩
          have hxy : y = x := hinj (hCA (hDC hy)) (hCA hx) he
          exact hxy ▸ hy
        · intro hx
          exact ⟨hDC hx,⟨x,hx,rfl⟩⟩
      exact he ▸ hr (f '' D) hsub ho
  · intro h
    constructor
    · apply (good_iff G C p).mpr
      intro D hDC ho
      rw [relImage_eq p A f hG (hDC.trans hCA)]
      exact (h D hDC).mp ho
    · apply (good_iff (swap (restrict G C)) (UnaryRelationFamilies.image G C) p).mpr
      intro E hEC ho
      rw [reverse_image_eq p A f hG hCA]
      let D : Set M := {x | x ∈ fibre C p ∧ f x ∈ E}
      have hDC : D ⊆ fibre C p := fun _ hx => hx.1
      have he : f '' D = E := by
        apply Set.Subset.antisymm
        · rintro y ⟨x,hx,rfl⟩
          exact hx.2
        · intro y hy
          have hy' : y ∈ f '' fibre C p := (Set.ext_iff.mp hImage y).mp (hEC hy)
          obtain ⟨x,hx,rfl⟩ := hy'
          exact ⟨x,⟨hx,hy⟩,rfl⟩
      exact (h D hDC).mpr (he.symm ▸ ho)

end IntegrationInACVF.Section3ACVF.ParameterizedOpenToOpen
