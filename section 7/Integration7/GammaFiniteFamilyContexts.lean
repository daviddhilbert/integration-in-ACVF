import Integration7.FiniteVolumeParameterContexts
import IntegrationSection5.FiniteGammaPresentation

/-! A finite family of original-Gamma sets has a presentation in a genuine
small containing context. The original Gamma base is retained. This refines
Section5.family_gamma_real_presentation by keeping track of its finite codes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gamma_finite_family_context
    (C : BaseContext M) (B : GammaParameters.Base (M := M))
    (hBC : B.real ⊆ (C.base : Set M)) {ι : Type} [Finite ι] {n m : ℕ}
    (U : ι → Set (Point (M := M) n m))
    (hU : ∀ i, GammaSetDefinable B (U i)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      ∃ A : ι → DefSet (M := M) (D.base : Set M) n m,
        ∀ i, carrier (A i) = U i := by
  choose d t ht A hA using fun i => gammaPresentationInput B (U i) (hU i)
  let E : Set M := ⋃ i, Set.range (GammaParameters.rawTuple (t i))
  have hE : E.Finite := Set.finite_iUnion fun i => Set.finite_range _
  let D := finiteVolumeParameterContext C E hE
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C E hE (Or.inl hx)
  have hAD (i : ι) : B.real ∪ Set.range (GammaParameters.rawTuple (t i)) ⊆
      (D.base : Set M) := by
    intro x hx
    rcases hx with hx | hx
    · exact hCD (hBC hx)
    · exact finiteVolumeParameterContext_contains C E hE
        (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  exact ⟨D, hCD, fun i => extendBase (A i) (hAD i), hA⟩

end IntegrationInACVF.Section7
