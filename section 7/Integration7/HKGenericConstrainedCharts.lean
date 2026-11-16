module

public import Integration7.HKConstrainedBijectionCharts
public import Integration7.GenericGammaWitnessCovers

@[expose] public section

/-! A density-constrained chart available on every genuinely generic VF
tuple glues to one original-base chart valid on all those tuples. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)}

theorem generic_bijection_chart_within {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hD : DefinableOverBase B (Fin.append (fun _ => .vf) sx) D)
    (hE : DefinableOverBase B (Fin.append (fun _ => .vf) sy) E)
    (K : Set (Fin ((p+a)+b) → M))
    (hrow : ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ C : GammaSortedBijectionChart B (fun _ => .vf) sx sy, C.carrier ⊆ K ∧ C.valid D E (vfValues x)) :
    ∃ C : GammaSortedBijectionChart B (fun _ => .vf) sx sy, C.carrier ⊆ K ∧
      ∀ x : Fin p → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
        C.valid D E (vfValues x) := by
  let I := {C : GammaSortedBijectionChart B (fun _ : Fin p => .vf) sx sy // C.carrier ⊆ K}
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B hκ hs hr hg
    (fun C : I => {z | C.val.valid D E z}) (fun C => C.val.valid_definable hD hE) (by
      intro x hx
      obtain ⟨C,hCK,hC⟩ := hrow x hx
      exact ⟨⟨C,hCK⟩,hC⟩)
  obtain ⟨C,hCK,hC⟩ := finite_bijection_glue_within hD hE K J
  exact ⟨C,hCK,fun x hx => hC (vfValues x) (hJ x hx)⟩

end IntegrationInACVF.Section7.HK
