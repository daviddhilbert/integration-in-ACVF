import IntegrationSection3ACVF.PromotedPartitionTemplates
import IntegrationSection3ACVF.FiniteBaseTupleCovers

/-! Pointwise valid original-base partition templates admit finitely many
uniform choices. Saturation is genuine and is used only after a common
finite real presentation of the interpreted base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.UniformPartitionTemplates

open PromotedPartitionTemplates

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_templates [Finite σ] {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite)
    (hsmall : Cardinal.mk B.real < κ) (G : Set (σ ⊕ Fin 2 → M))
    (hG : FullBaseAtomicity.OverBase B G)
    (hLocal : ∀ p : σ → M, ∃ T : Template M σ, Definable B T ∧ p ∈ locus G T) :
    ∃ F : Finset (Template M σ), (∀ T ∈ F, Definable B T) ∧
      ∀ p : σ → M, ∃ T ∈ F, p ∈ locus G T := by
  classical
  let C : Set (Set (σ → M)) := {U | ∃ T : Template M σ, Definable B T ∧ locus G T = U}
  have hC (U : Set (σ → M)) (hU : U ∈ C) : FullBaseAtomicity.OverBase B U := by
    obtain ⟨T,hT,rfl⟩ := hU
    exact UnaryPartitionTemplates.valid_definable B hG hT
  have hCov (p : σ → M) (_ : p ∈ (Set.univ : Set (σ → M))) : ∃ U ∈ C, p ∈ U := by
    obtain ⟨T,hT,hp⟩ := hLocal p
    exact ⟨locus G T,⟨T,hT,rfl⟩,hp⟩
  have hu : FullBaseAtomicity.OverBase B (Set.univ : Set (σ → M)) := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact Set.definable_univ
  obtain ⟨H,hH,hCovH⟩ := FiniteBaseTupleCovers.finite_subcover hκ hs B hB hsmall Set.univ hu C hC hCov
  choose T hT hEq using fun U : H => hH U.val U.property
  let F := H.attach.image T
  refine ⟨F,?_,?_⟩
  · intro t ht
    obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp ht
    exact hT U
  · intro p
    obtain ⟨U,hUH,hpU⟩ := hCovH p (Set.mem_univ p)
    refine ⟨T ⟨U,hUH⟩,Finset.mem_image.mpr ⟨⟨U,hUH⟩,Finset.mem_attach _ _,rfl⟩,?_⟩
    exact (Set.ext_iff.mp (hEq ⟨U,hUH⟩) p).mpr hpU

end IntegrationInACVF.Section3ACVF.UniformPartitionTemplates
