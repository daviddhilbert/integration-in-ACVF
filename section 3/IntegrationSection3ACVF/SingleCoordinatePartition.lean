import IntegrationSection3ACVF.CoordinatePairGluing

/-! The full original-base finite coordinate partition for one pair.
Only finite formula support is used internally; there is no cardinal or
finiteness condition on the set of originally named imaginaries. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.SingleCoordinatePartition

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_base [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite)
    (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (hSrcVF : ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ x ∈ A, iVF (f x j)) :
    ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ CoordinateOpenToOpen.At W f i j) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
  obtain ⟨F,hF,hCov⟩ := CoordinatePartitionTemplates.finite_templates hκ hs B hB hsmall h00 δ hδ hδ1
    A f hf hinj i j hSrcVF hTarVF
  obtain ⟨K,hK,hDisK,hCovK⟩ := PartitionTemplateCases.exists_cases B (CoordinatePartitionTemplates.graph A f i j)
    (CoordinateFibreSyntax.graph_definable B A f hf i j) F hF hCov
  exact CoordinatePairGluing.exists_partition B A f hf hinj i j K
    (fun U hU => (hK U hU).2) hDisK hCovK

theorem full_base [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (hSrcVF : ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ x ∈ A, iVF (f x j)) :
    ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ CoordinateOpenToOpen.At W f i j) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
  classical
  obtain ⟨FF,hFF,hFData⟩ := hf
  obtain ⟨FG,hFG,hGData⟩ := hδ
  let F := FF ∪ FG
  let B0 : FullBaseAtomicity.Base (M := M) := ⟨B.real,(F : Set (ParameterPresentation.Name (M := M)))⟩
  have hf0 : FullBaseAtomicity.OverBase B0 (FiniteTupleGraphs.graph A f) :=
    ⟨FF,fun i hi => Finset.mem_union.mpr (Or.inl hi),hFData⟩
  have hδ0 : FullGammaSyntax.Scalar B0 {δ} :=
    ⟨FG,fun i hi => Finset.mem_union.mpr (Or.inr hi),hGData⟩
  have hB0 : B0.imaginary ⊆ B.imaginary := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hFF i hi
    · exact hFG i hi
  obtain ⟨P,hP,hDis,hCov⟩ := finite_base hκ hs B0 F.finite_toSet hsmall h00 δ hδ0 hδ1
    A f hf0 hinj i j hSrcVF hTarVF
  refine ⟨P,?_,hDis,hCov⟩
  intro W hW
  obtain ⟨hne,hWA,hDef,hAt⟩ := hP W hW
  exact ⟨hne,hWA,FullBaseAtomicity.OverBase.mono hDef Set.Subset.rfl hB0,hAt⟩

end IntegrationInACVF.Section3ACVF.SingleCoordinatePartition
