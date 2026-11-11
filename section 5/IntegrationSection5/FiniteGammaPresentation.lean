import IntegrationSection5.GammaMapPresentation

/-! A common internal real presentation for a family of original-Gamma sets.
The enlarged code set is not a new smallness or original-base hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}

theorem family_gamma_real_presentation {ι : Type} (U : ι → Set (Point (M := M) n m))
    (hU : ∀ i, GammaSetDefinable P (U i)) (hPS : P.real ⊆ S) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ D : ι → DefSet (M := M) R n m,
      ∀ i, carrier (D i) = U i := by
  choose d t ht D hD using fun i => gammaPresentationInput P (U i) (hU i)
  let R := S ∪ ⋃ i, Set.range (GammaParameters.rawTuple (t i))
  have hSR : S ⊆ R := Set.subset_union_left
  have hDR (i : ι) : P.real ∪ Set.range (GammaParameters.rawTuple (t i)) ⊆ R := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hPS hx)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,hx⟩)
  exact ⟨R,hSR,fun i => extendBase (D i) (hDR i),hD⟩

end IntegrationInACVF.Section5
