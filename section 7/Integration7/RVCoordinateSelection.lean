import Section4.RVCoordinates
import Section4.Products
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {a b : ℕ}

def rvCoordinateSelectMap (S : Set M) (ρ : Fin b → Fin a) :
    Map (DefSet.univ (rawRVSpace (M := M) a) S) (DefSet.univ (rawRVSpace (M := M) b) S) := by
  refine Map.ofCodes _ (fun t => t ∘ ρ) (fun z => z ∘ ρ)
    (fun i => Set.DefinableFun.proj LRV) ?_ ?_
  · intro c
    exact ⟨(rawRVSpace (M := M) a).decode c ∘ ρ,
      congrArg (fun z => z ∘ ρ) (rvValues_decode c)⟩
  · intro c
    apply rvValues_injective
    exact (rvValues_decode _).trans (congrArg (fun z => z ∘ ρ) (rvValues_decode c)).symm

@[simp] theorem rvCoordinateSelectMap_value (S : Set M) (ρ : Fin b → Fin a)
    (t : DefSet.univ (rawRVSpace (M := M) a) S) :
    (rvCoordinateSelectMap S ρ t).val=t.val ∘ ρ := rfl
end IntegrationInACVF.Section7
