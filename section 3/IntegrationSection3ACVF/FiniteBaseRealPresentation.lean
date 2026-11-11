import IntegrationSection3ACVF.FullBaseDefinability

/-! A finite interpreted base has a common finite real presentation for
all its definitions. The codes are used only inside compactness arguments;
original-base definability remains the final conclusion. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FiniteBaseRealPresentation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_common_codes (B : FullBaseAtomicity.Base (M := M)) (hB : B.imaginary.Finite) :
    ∃ E : Set M, E.Finite ∧
      ∀ (α : Type) [Finite α] (D : Set (α → M)), FullBaseAtomicity.OverBase B D →
        @Set.Definable M (B.real ∪ E) LRV (@CanonicalStructure.normalize M sM) α D := by
  classical
  let p := @ParameterPresentation.presentation M sM hM
  letI := hB.fintype
  choose code hCode using fun i : B.imaginary => p.onto i.val
  let E : Set M := Set.range (fun z : B.imaginary × Fin 5 => (code z.1).val z.2)
  refine ⟨E,Set.finite_range _,?_⟩
  intro α _ D hD
  obtain ⟨F,hF,R,hR,hRD⟩ := hD
  let q := ImaginaryParameters.tuplePresentation p F
  let c : q.codes :=
    ⟨fun z => (code ⟨z.1.val,hF z.1.val z.1.property⟩).val z.2,
      fun i => (code ⟨i.val,hF i.val i.property⟩).property⟩
  have hc : q.decode c = (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
    funext i
    exact hCode ⟨i.val,hF i.val i.property⟩
  have hEq : R (q.decode c) = D := hc ▸ hRD
  let S := B.real ∪ E
  have hRange (z : F × Fin 5) : c.val z ∈ S :=
    Or.inr ⟨(⟨z.1.val,hF z.1.val z.1.property⟩,z.2),rfl⟩
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have hR' : @Set.Definable M S LRV N ((F × Fin 5) ⊕ α)
      (ImaginaryParameters.vectorPullback q R) := hR.mono Set.subset_union_left
  let g : (α → M) → (F × Fin 5) ⊕ α → M := fun z => Sum.elim c.val z
  have hg : S.DefinableMap LRV g := by
    intro j
    cases j with
    | inl j => exact LRV.definableFun_const α (hRange j)
    | inr j => exact Set.DefinableFun.proj LRV
  convert hR'.preimage_map hg using 1
  ext z
  change z ∈ D ↔ ∃ h : c.val ∈ q.codes, z ∈ R (q.decode ⟨c.val,h⟩)
  rw [← hEq]
  exact ⟨fun hz => ⟨c.property,hz⟩,fun ⟨_,hz⟩ => hz⟩

end IntegrationInACVF.Section3ACVF.FiniteBaseRealPresentation
