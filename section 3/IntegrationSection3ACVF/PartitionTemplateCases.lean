import IntegrationSection3ACVF.UniformPartitionTemplates
import IntegrationSection3.DefinablePartitions

/-! Finitely many uniform partition templates can be assigned on disjoint
original-base definable parameter cases. Every case lies in the validity
locus of its assigned template. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.PartitionTemplateCases

open PromotedPartitionTemplates

variable {M σ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_cases [Finite σ] (B : FullBaseAtomicity.Base (M := M))
    (G : Set (σ ⊕ Fin 2 → M)) (hG : FullBaseAtomicity.OverBase B G)
    (F : Finset (Template M σ)) (hF : ∀ T ∈ F, Definable B T)
    (hCov : ∀ p : σ → M, ∃ T ∈ F, p ∈ locus G T) :
    ∃ K : Finset (Set (σ → M)),
      (∀ U ∈ K, U.Nonempty ∧ FullBaseAtomicity.OverBase B U ∧
        ∃ T : Template M σ, Definable B T ∧ U ⊆ locus G T) ∧
      (K : Set (Set (σ → M))).Pairwise Disjoint ∧
      ∀ p : σ → M, ∃ U ∈ K, p ∈ U := by
  classical
  let L := F.image (locus G)
  have hL (U : Set (σ → M)) (hU : U ∈ L) : FullBaseAtomicity.OverBase B U := by
    obtain ⟨T,hTF,rfl⟩ := Finset.mem_image.mp hU
    exact UnaryPartitionTemplates.valid_definable B hG (hF T hTF)
  have hCover (p : σ → M) (_ : p ∈ (Set.univ : Set (σ → M))) : ∃ U ∈ L, p ∈ U := by
    obtain ⟨T,hTF,hpT⟩ := hCov p
    exact ⟨locus G T,Finset.mem_image.mpr ⟨T,hTF,rfl⟩,hpT⟩
  have hTop : FullBaseAtomicity.OverBase B (Set.univ : Set (σ → M)) := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact Set.definable_univ
  let p := @ParameterPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hPart : ∃ K : Finset (Set (σ → M)),
      (∀ U ∈ K, U.Nonempty ∧ U ⊆ Set.univ ∧ FullBaseAtomicity.OverBase B U ∧ ∃ V ∈ L, U ⊆ V) ∧
      (K : Set (Set (σ → M))).Pairwise Disjoint ∧ Set.univ = {z | ∃ U ∈ K, z ∈ U} := by
    letI := @CanonicalStructure.normalize M sM
    exact DefinablePartitions.exists_partition (p := p) (B := B) hp hTop L hL hCover
  obtain ⟨K,hK,hDis,hEq⟩ := hPart
  refine ⟨K,?_,hDis,?_⟩
  · intro U hUK
    obtain ⟨hne,_,hDef,V,hVL,hUV⟩ := hK U hUK
    obtain ⟨T,hTF,rfl⟩ := Finset.mem_image.mp hVL
    exact ⟨hne,hDef,T,hF T hTF,hUV⟩
  · intro z
    exact (Set.ext_iff.mp hEq z).mp (Set.mem_univ z)

end IntegrationInACVF.Section3ACVF.PartitionTemplateCases
