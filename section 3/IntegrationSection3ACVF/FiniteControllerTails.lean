import IntegrationSection3ACVF.FullGammaControllers

/-! A finite-range relation with controlled value-group rows has a tail
contained in one row. No completeness or Archimedean assumption is used. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.FiniteControllerTails

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem eventual_label {J : Type} (R : Values.Gamma (M := M) → J → Prop)
    (α : Values.Gamma (M := M))
    (hfinite : {c : J | ∃ γ, R γ c}.Finite)
    (hDomain : ∀ γ, α < γ → ∃ c, R γ c)
    (hControls : ∀ c, ∃ F, FiniteOrder.Controls F {γ | R γ c}) :
    ∃ η : Values.Gamma (M := M), α < η ∧ ∃ c : J, ∀ γ, η < γ → R γ c := by
  choose F hF using hControls
  let E : Set (Values.Gamma (M := M)) := ⋃ c ∈ {c : J | ∃ γ, R γ c}, (F c : Set (Values.Gamma (M := M)))
  have hE : E.Finite := hfinite.biUnion (fun c _ => (F c).finite_toSet)
  obtain ⟨u,hu⟩ := hE.bddAbove
  obtain ⟨η,hη⟩ := exists_gt (max α u)
  obtain ⟨θ,hθ⟩ := exists_gt η
  obtain ⟨c,hc⟩ := hDomain θ (lt_of_le_of_lt (le_max_left α u) (hη.trans hθ))
  refine ⟨η,lt_of_le_of_lt (le_max_left α u) hη,c,fun γ hγ => ?_⟩
  have hcRange : c ∈ {c : J | ∃ γ, R γ c} := ⟨θ,hc⟩
  have hPattern : FiniteOrder.Pattern (F c) θ γ := by
    intro p hp
    have hpE : p ∈ E := Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hcRange,hp⟩⟩
    have hpη : p < η := lt_of_le_of_lt (hu hpE) (lt_of_le_of_lt (le_max_right α u) hη)
    have hpθ := hpη.trans hθ
    have hpγ := hpη.trans hγ
    exact ⟨iff_of_false (not_lt_of_ge hpθ.le) (not_lt_of_ge hpγ.le),iff_of_true hpθ hpγ⟩
  exact (hF c θ γ hPattern).mp hc

end IntegrationInACVF.Section3ACVF.FiniteControllerTails
