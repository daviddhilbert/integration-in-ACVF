import IntegrationSection3ACVF.FullBaseDefinability
import Section3.SmallFiniteParameters

/-! Finite real context labels may be named while retaining every old
imaginary parameter. Actual full relation fibres and smallness are proved. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RealParameterTuples

variable {M α β : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def extend (B : FullBaseAtomicity.Base (M := M)) (a : α → M) : FullBaseAtomicity.Base (M := M) :=
  ⟨B.real ∪ Set.range a,B.imaginary⟩

theorem mono (B : FullBaseAtomicity.Base (M := M)) (a : α → M)
    {D : Set (β → M)} (hD : FullBaseAtomicity.OverBase B D) :
    FullBaseAtomicity.OverBase (extend B a) D :=
  FullBaseAtomicity.OverBase.mono hD Set.subset_union_left Set.Subset.rfl

theorem specialize [Finite α] [Finite β] (B : FullBaseAtomicity.Base (M := M)) (a : α → M)
    {D : Set (α ⊕ β → M)} (hD : FullBaseAtomicity.OverBase B D) :
    FullBaseAtomicity.OverBase (extend B a) {z : β → M | Sum.elim a z ∈ D} := by
  have hD' := mono B a hD
  have hg : @Set.DefinableMap M LRV (@CanonicalStructure.normalize M sM) β (α ⊕ β)
      (extend B a).real (fun z => Sum.elim a z) := by
    letI := @CanonicalStructure.normalize M sM
    intro j
    cases j with
    | inl j => exact LRV.definableFun_const β (Or.inr ⟨j,rfl⟩)
    | inr j => exact Set.DefinableFun.proj LRV
  exact FullBaseAtomicity.OverBase.preimage_map hD' hg

theorem small [Finite α] {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (B : FullBaseAtomicity.Base (M := M)) (hB : Cardinal.mk B.real < κ) (a : α → M) :
    Cardinal.mk (extend B a).real < κ :=
  small_union_finite hκ B.real hB _ (Set.finite_range a)

end IntegrationInACVF.Section3ACVF.RealParameterTuples
