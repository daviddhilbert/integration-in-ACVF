import Section5.GammaInvariantLogic
import IntegrationSection6.RVLabelMap

/-! Restricting a real-definable coordinate program to an original-Gamma
source retains its complete invariant graph, without naming that source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m u w : ℕ}

theorem gamma_map_graph_of_global_formula
    {A : DefSet (M := M) S n m} {C : DefSet (M := M) S u w} (F : Map A C)
    (G : Map (PresentedSet.univ (pointSpace n m) B.real)
      (PresentedSet.univ (pointSpace u w) B.real))
    (hA : GammaSetDefinable B (carrier A))
    (hF : ∀ a : A, (F a).val = (G ⟨a.val,Set.mem_univ _⟩).val) :
    GammaGraphDefinable B (pointMapGraph F) := by
  let L := gammaLogicInput B
  apply GammaGraphDefinable.congr (L.restrict_graph hA (L.real_map_graph G))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    exact (hF ⟨p,hp⟩).trans ((congrArg (fun b => (G b).val) (Subtype.ext ha.symm)).trans hq)
  · rintro ⟨a,ha,hq⟩
    refine ⟨ha ▸ a.property,⟨p,Set.mem_univ _⟩,rfl,?_⟩
    exact ((congrArg (fun b => (G b).val) (Subtype.ext ha.symm)).trans (hF a).symm).trans hq

end IntegrationInACVF.Section6
