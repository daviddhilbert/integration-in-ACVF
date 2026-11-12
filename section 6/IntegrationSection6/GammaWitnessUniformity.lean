import Section3.GammaFullDescent
import Section3.TupleCompactness
import Mathlib.Data.Finset.Lattice.Fold

/-! Genuine compactness for original-Gamma definable witness loci.
Only the original real and Gamma names are bounded, never all proper
RV codes or an arbitrary internal presentation. This is the finite-cover
ingredient for6.14, not the still-needed encoding of its blowup witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_definable_finite_subcover {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    (C : Set (Set (Fin n → M))) (hC : ∀ c ∈ C, DefinableOverBase B sn c)
    (hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) :
    ∃ C₀ : Set (Set (Fin n → M)), C₀.Finite ∧ C₀ ⊆ C ∧ ∀ a ∈ A, ∃ c ∈ C₀, a ∈ c := by
  have hNames := commonRealNames_small hκ B hreal hgamma
  have hAN := (definableOver_iff_normalized_raw (commonRealNames B) sn A).mp hA.common_names
  have hCN (c : Set (Fin n → M)) (hc : c ∈ C) :=
    ((definableOver_iff_normalized_raw (commonRealNames B) sn c).mp (hC c hc).common_names).1
  exact @Saturated.definable_finite_subcover_tuple M N κ (@Saturated.normalize M sM κ hs)
    (commonRealNames B) hNames n A hAN.1 C hCN hcover

theorem gamma_finite_witnesses {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    {I : Type*} (valid : I → Set (Fin n → M)) (hvalid : ∀ i, DefinableOverBase B sn (valid i))
    (hcover : ∀ a ∈ A, ∃ i, a ∈ valid i) :
    ∃ J : Finset I, ∀ a ∈ A, ∃ i ∈ J, a ∈ valid i := by
  obtain ⟨C₀,hfin,hsub,hcov⟩ := gamma_definable_finite_subcover hκ hs hreal hgamma sn A hA
    (Set.range valid) (by rintro _ ⟨i,rfl⟩; exact hvalid i)
    (by intro a ha; obtain ⟨i,hi⟩ := hcover a ha; exact ⟨valid i,Set.mem_range_self i,hi⟩)
  letI := hfin.fintype
  have hchoice (c : C₀) : ∃ i, valid i = c.val := hsub c.property
  choose index hindex using hchoice
  refine ⟨Finset.univ.image index,?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hcov a ha
  exact ⟨index ⟨c,hc⟩,Finset.mem_image.mpr ⟨⟨c,hc⟩,Finset.mem_univ _,rfl⟩,
    (hindex ⟨c,hc⟩).symm ▸ hac⟩

theorem gamma_uniform_witness_length {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sn : Fin n → SortTag) (A : Set (Fin n → M)) (hA : DefinableOverBase B sn A)
    {I : Type*} (valid : I → Set (Fin n → M)) (hvalid : ∀ i, DefinableOverBase B sn (valid i))
    (length : I → ℕ) (hcover : ∀ a ∈ A, ∃ i, a ∈ valid i) :
    ∃ J : Finset I, ∃ bound : ℕ, ∀ a ∈ A, ∃ i ∈ J, length i ≤ bound ∧ a ∈ valid i := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hreal hgamma sn A hA valid hvalid hcover
  refine ⟨J,J.sup length,?_⟩
  intro a ha
  obtain ⟨i,hi,hvalid⟩ := hJ a ha
  exact ⟨i,hi,Finset.le_sup hi,hvalid⟩

end IntegrationInACVF.Section6
