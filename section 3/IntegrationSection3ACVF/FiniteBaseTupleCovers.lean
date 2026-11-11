import IntegrationSection3ACVF.FiniteBaseRealPresentation
import IntegrationSection3ACVF.RealOpenImageCovers
import Section3.TupleCompactness

/-! Genuine finite-subcover compactness for arbitrary finite tuple indices
over a finite interpreted base. Auxiliary real codes are internal. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FiniteBaseTupleCovers

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_subcover [Finite σ] {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite)
    (hsmall : Cardinal.mk B.real < κ) (A : Set (σ → M))
    (hA : FullBaseAtomicity.OverBase B A) (C : Set (Set (σ → M)))
    (hC : ∀ D ∈ C, FullBaseAtomicity.OverBase B D)
    (hCov : ∀ a ∈ A, ∃ D ∈ C, a ∈ D) :
    ∃ F : Finset (Set (σ → M)), (∀ D ∈ F, D ∈ C) ∧ ∀ a ∈ A, ∃ D ∈ F, a ∈ D := by
  classical
  letI := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  let pull (D : Set (σ → M)) : Set (Fin (Fintype.card σ) → M) :=
    (fun z => z ∘ e) ⁻¹' D
  let push (D : Set (Fin (Fintype.card σ) → M)) : Set (σ → M) :=
    (fun z => z ∘ e.symm) ⁻¹' D
  have hInv (D : Set (σ → M)) : push (pull D) = D := by
    ext z
    change (z ∘ e.symm ∘ e ∈ D) ↔ z ∈ D
    have he : z ∘ e.symm ∘ e = z := by funext k; simp only [Function.comp_apply,e.symm_apply_apply]
    rw [he]
  obtain ⟨E,hE,hPresentation⟩ := FiniteBaseRealPresentation.exists_common_codes B hB
  let S := B.real ∪ E
  have hSmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall E hE
  let N := @CanonicalStructure.normalize M sM
  letI := sM
  have hRaw {D : Set (σ → M)} (hD : FullBaseAtomicity.OverBase B D) :
      @Set.Definable M S LRV N (Fin (Fintype.card σ)) (pull D) := by
    letI := N
    exact (hPresentation σ D hD).preimage_comp e
  have hCover : ∀ z ∈ pull A, ∃ D ∈ pull '' C, z ∈ D := by
    intro z hz
    obtain ⟨D,hD,hzD⟩ := hCov (z ∘ e) hz
    exact ⟨pull D,⟨D,hD,rfl⟩,hzD⟩
  obtain ⟨F,hF,hFC,hCovF⟩ := @Saturated.definable_finite_subcover_tuple M N κ
    hs.normalize S hSmallS (Fintype.card σ) (pull A) (hRaw hA) (pull '' C)
      (by rintro D ⟨D,hD,rfl⟩; exact hRaw (hC D hD)) hCover
  let H := F.image push
  have hH : H.Finite := hF.image push
  refine ⟨hH.toFinset,?_,?_⟩
  · intro D hD
    obtain ⟨U,hUF,rfl⟩ := hH.mem_toFinset.mp hD
    obtain ⟨V,hVC,rfl⟩ := hFC hUF
    rw [hInv]
    exact hVC
  · intro a ha
    have hpA : a ∘ e.symm ∈ pull A := by
      change a ∈ push (pull A)
      rwa [hInv]
    obtain ⟨D,hDF,haD⟩ := hCovF (a ∘ e.symm) hpA
    exact ⟨push D,hH.mem_toFinset.mpr ⟨D,hDF,rfl⟩,haD⟩

end IntegrationInACVF.Section3ACVF.FiniteBaseTupleCovers
