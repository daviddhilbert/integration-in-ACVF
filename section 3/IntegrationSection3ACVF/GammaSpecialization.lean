import IntegrationSection3ACVF.AdjoinGamma

/-! Specializing a finite Gamma-only parameter support uses RV representatives
and only the original VF constants0/1. No new VF coefficient is named. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3.ImaginaryParameters

namespace IntegrationInACVF.Section3ACVF.GammaSpecialization

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem specialize (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {α : Type} [Finite α] {A : Set (α → M)} (hA : FullBaseAtomicity.OverBase B A) :
    ∃ T : Set M, T.Finite ∧
      @Set.Definable M (B.real ∪ T) LRV (@CanonicalStructure.normalize M sM) α A ∧
        ∀ x ∈ T, @iRV M sM x ∨ x = @iVFZero M sM ∨ x = @iVFOne M sM := by
  classical
  obtain ⟨F,hF,R,hR,hRA⟩ := hA
  have hGamma (j : F) : ∃ γ : Values.Gamma (M := M), j.val = Sum.inr γ :=
    hOnly j.val (hF j.val j.property)
  choose γ hγ using hGamma
  choose t ht hval using fun j : F => GammaParameters.EndpointLogic.codeValue_surjective (γ j)
  let c (j : F) : ParameterPresentation.codeDomain (M := M) :=
    ⟨AdjoinGamma.embedCode ![t j],(AdjoinGamma.embedCode_compatible ![t j] (ht j)).choose⟩
  have hc (j : F) : ParameterPresentation.decode (c j) = j.val := by
    have he := (AdjoinGamma.embedCode_compatible (M := M) ![t j] (ht j)).choose_spec
    exact he.trans ((congrArg Sum.inr (hval j)).trans (hγ j).symm)
  let p := @ParameterPresentation.presentation M sM hM
  let q := ImaginaryParameters.tuplePresentation p F
  let z : q.codes := ⟨fun u => (c u.1).val u.2,fun j => (c j).property⟩
  have hz : q.decode z = (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
    funext j
    exact hc j
  have hZA : R (q.decode z) = A := by
    rw [hz]
    exact hRA
  let T : Set M := Set.range z.val
  have hT : T.Finite := Set.finite_range z.val
  have hclass : ∀ x ∈ T, @iRV M sM x ∨ x = @iVFZero M sM ∨ x = @iVFOne M sM := by
    rintro x ⟨⟨j,k⟩,rfl⟩
    change iRV (AdjoinGamma.embedCode ![t j] k) ∨
      AdjoinGamma.embedCode ![t j] k = iVFZero ∨ AdjoinGamma.embedCode ![t j] k = iVFOne
    fin_cases k
    · exact Or.inl (ht j).1
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  let f : (α → M) → ((F × Fin 5) ⊕ α → M) := fun a => Sum.elim z.val a
  let N := @CanonicalStructure.normalize M sM
  have hR' : @Set.Definable M (B.real ∪ T) LRV N ((F × Fin 5) ⊕ α)
      (ImaginaryParameters.vectorPullback q R) := hR.mono Set.subset_union_left
  have hf : @Set.DefinableMap M LRV N α ((F × Fin 5) ⊕ α) (B.real ∪ T) f := by
    letI := N
    intro j
    cases j with
    | inl j => exact LRV.definableFun_const α (Or.inr ⟨j,rfl⟩)
    | inr j => exact Set.DefinableFun.proj LRV
  have hout : @Set.Definable M (B.real ∪ T) LRV N α A := by
    letI := N
    convert hR'.preimage_map hf using 1
    ext a
    change a ∈ A ↔ ∃ h : z.val ∈ q.codes, a ∈ R (q.decode ⟨z.val,h⟩)
    rw [← hZA]
    exact ⟨fun ha => ⟨z.property,ha⟩,fun ⟨_,ha⟩ => ha⟩
  exact ⟨T,hT,hout,hclass⟩

theorem parameterField_unchanged (A T : Set M)
    (hT : ∀ x ∈ T, iRV x ∨ x = iVFZero ∨ x = iVFOne) :
    vfParameterField (A ∪ T) = vfParameterField A := by
  unfold vfParameterField
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    intro x hx
    rcases hx with hx | hx
    · exact Subfield.subset_closure hx
    · rcases hT x.val hx with hr | hz | ho
      · have hs : SortTag.vf = SortTag.rv :=
          CanonicalStructure.sort_unique hM x.property hr
        cases hs
      · have hx0 : x = 0 := Subtype.ext hz
        rw [hx0]
        exact Subfield.zero_mem _
      · have hx1 : x = 1 := Subtype.ext ho
        rw [hx1]
        exact Subfield.one_mem _
  · exact Subfield.closure_mono (fun x hx => Or.inl hx)

theorem specialize_preserving_field (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {α : Type} [Finite α] {A : Set (α → M)} (hA : FullBaseAtomicity.OverBase B A) :
    ∃ T : Set M, T.Finite ∧
      @Set.Definable M (B.real ∪ T) LRV (@CanonicalStructure.normalize M sM) α A ∧
        vfParameterField (B.real ∪ T) = vfParameterField B.real := by
  obtain ⟨T,hfin,hdef,hT⟩ := specialize B hOnly hA
  exact ⟨T,hfin,hdef,parameterField_unchanged B.real T hT⟩

end IntegrationInACVF.Section3ACVF.GammaSpecialization
