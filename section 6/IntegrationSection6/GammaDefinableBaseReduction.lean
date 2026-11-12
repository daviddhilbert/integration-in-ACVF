import IntegrationSection6.GammaSortedParameterElimination
import IntegrationSection6.GammaFormulaBaseChange
import IntegrationSection6.FiniteGammaObjects

/-! Eliminate definable names from the mathematical Gamma base while
retaining the same actual native finite objects and internal code sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaDefinableBaseReduction (C B : Base (M := M)) where
  real_subset : B.real ⊆ C.real
  real_definable : ∀ c ∈ C.real, ∀ σ, sortEval σ c → DefinableClosureAtBase B σ c
  gamma_definable : ∀ γ ∈ C.gamma, GammaDefinableClosureAtBase B γ

variable {B C : Base (M := M)} {S : Set M} {n : ℕ}

theorem GammaDefinableBaseReduction.definable (H : GammaDefinableBaseReduction C B)
    {r : ℕ} {sn : Fin r → SortTag} {D : Set (Fin r → M)} (hD : DefinableOverBase C sn D) :
    DefinableOverBase B sn D :=
  gamma_eliminate_sorted_real_params hD H.real_definable H.gamma_definable

def GammaDefinableBaseReduction.formulas (H : GammaDefinableBaseReduction C B) : GammaFormulaBaseChange C B :=
  ⟨fun _ _ hD => H.definable hD⟩

def GammaDefinableBaseReduction.objectAt (H : GammaDefinableBaseReduction C B)
    (U : FiniteRV.GammaObjectAt C S n) : FiniteRV.GammaObjectAt B S n where
  object := U.object
  real_contains := fun c hc => U.real_contains (H.real_subset hc)
  domain_graph := H.definable U.domain_graph
  volume_graph := H.definable U.volume_graph

def GammaDefinableBaseReduction.finiteObject (H : GammaDefinableBaseReduction C B)
    (U : GammaRVFiniteObject C n) : GammaRVFiniteObject B n where
  codes := U.codes
  real_contains := fun c hc => U.real_contains (H.real_subset hc)
  object := U.object
  domain_graph := H.definable U.domain_graph
  volume_graph := H.definable U.volume_graph
  finite_volume := U.finite_volume

theorem GammaDefinableBaseReduction.coordinate_algebraic (H : GammaDefinableBaseReduction C B)
    (i : Fin n) (t : Fin n → RV (M := M)) (z : M)
    (hz : AlgebraicAtBase ⟨coordinateBase C.real i t,C.gamma⟩ .rv z) :
    AlgebraicAtBase ⟨coordinateBase B.real i t,B.gamma⟩ .rv z := by
  obtain ⟨D,hD,hFinite,hz⟩ := hz
  refine ⟨D,gamma_eliminate_sorted_real_params hD ?_ ?_,hFinite,hz⟩
  · intro c hc σ hσ
    rcases hc with hc | hc
    · exact (H.real_definable c hc σ hσ).mono Set.subset_union_left (Set.Subset.refl _)
    · exact real_definableAtBase _ σ _ (definableClosureAt_of_mem (Or.inr hc) hσ)
  · intro γ hγ
    exact (H.gamma_definable γ hγ).mono Set.subset_union_left (Set.Subset.refl _)

def GammaDefinableBaseReduction.admissible (H : GammaDefinableBaseReduction C B)
    (U : GammaRVFiniteObject C n) (i : Fin n) (hAd : GammaAdmissible U.toGammaRVObject i) :
    GammaAdmissible (H.finiteObject U).toGammaRVObject i :=
  ⟨hAd.nonzero,fun u => H.coordinate_algebraic i (SpecialTransformations.Section7.gammaVolumeValue U.toGammaRVObject u) _ (hAd.algebraic u)⟩

end IntegrationInACVF.Section6
