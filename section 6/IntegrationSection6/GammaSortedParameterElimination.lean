import Section3.GammaClosureLaws

/-! Eliminate additional definable real names while retaining the original
real/Gamma base and its full invariant formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_eliminate_sorted_real_params {B C : Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {D : Set (Fin n → M)} (hD : DefinableOverBase C sn D)
    (hReal : ∀ c ∈ C.real, ∀ σ, sortEval σ c → DefinableClosureAtBase B σ c)
    (hGamma : ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase B γ) : DefinableOverBase B sn D := by
  apply hD.eliminate_definable_params ?_ hGamma
  intro c hc
  rcases TypedModelMap.sort_cover (M := M) c with hv | hr
  · exact ⟨.vf,hReal c hc .vf hv⟩
  · exact ⟨.rv,hReal c hc .rv hr⟩

theorem gamma_eliminate_added_real {B : Base (M := M)} {E : Set M} {n : ℕ}
    {sn : Fin n → SortTag} {D : Set (Fin n → M)}
    (hD : DefinableOverBase ⟨B.real ∪ E,B.gamma⟩ sn D)
    (hE : ∀ c ∈ E, ∀ σ, sortEval σ c → DefinableClosureAtBase B σ c) : DefinableOverBase B sn D := by
  apply gamma_eliminate_sorted_real_params hD ?_ ?_
  · intro c hc σ hσ
    rcases hc with hc | hc
    · exact real_definableAtBase B σ _ (definableClosureAt_of_mem hc hσ)
    · exact hE c hc σ hσ
  · intro γ hγ
    exact gamma_name_definable B γ hγ

end IntegrationInACVF.Section6
