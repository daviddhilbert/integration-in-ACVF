import IntegrationSection3ACVF.FullBaseAtomicity

/-! First-order closure operations over the combined interpreted base.
These wrappers keep the original model separate from its normalization. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.FullBaseAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {α β : Type} [Finite α] [Finite β]

theorem OverBase.of_real {A : Set (α → M)}
    (hA : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) α A) :
    OverBase B A := by
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.of_real (p := p) hA

omit [Finite α] in
theorem OverBase.congr {A C : Set (α → M)} (hA : OverBase B A)
    (h : ∀ a, a ∈ A ↔ a ∈ C) : OverBase B C := Set.ext h ▸ hA

theorem OverBase.inter {A C : Set (α → M)} (hA : OverBase B A) (hC : OverBase B C) :
    OverBase B (A ∩ C) := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.inter hA hC hp

theorem OverBase.compl {A : Set (α → M)} (hA : OverBase B A) : OverBase B Aᶜ := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.compl hA hp

theorem OverBase.union {A C : Set (α → M)} (hA : OverBase B A) (hC : OverBase B C) :
    OverBase B (A ∪ C) := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  have h := ImaginaryParameters.OverBase.compl
    (ImaginaryParameters.OverBase.inter
      (ImaginaryParameters.OverBase.compl hA hp)
      (ImaginaryParameters.OverBase.compl hC hp) hp) hp
  convert h using 1
  ext z
  simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_inter_iff,not_and_or,not_not]

omit [Finite α] [Finite β] in
theorem OverBase.preimage_comp {A : Set (α → M)} (hA : OverBase B A) (f : α → β) :
    OverBase B ((fun z : β → M => z ∘ f) ⁻¹' A) := by
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.preimage_comp hA f

omit [Finite α] in
theorem OverBase.exists_block {A : Set (α ⊕ β → M)} (hA : OverBase B A) :
    OverBase B {z | ∃ b : β → M, Sum.elim z b ∈ A} := by
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.exists_block hA

theorem OverBase.forall_block {A : Set (α ⊕ β → M)} (hA : OverBase B A) :
    OverBase B {z | ∀ b : β → M, Sum.elim z b ∈ A} := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.forall_block hA hp

theorem OverBase.forall_finite {τ : Type} [Finite τ] {P : τ → Set (α → M)}
    (hP : ∀ t, OverBase B (P t)) : OverBase B {z | ∀ t, z ∈ P t} := by
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.forall_finite hP hp

end IntegrationInACVF.Section3ACVF.FullBaseAtomicity
