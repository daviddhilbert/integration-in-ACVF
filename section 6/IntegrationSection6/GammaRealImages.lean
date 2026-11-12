import Section5.GammaLift
import Section5.GammaInvariantLogic

/-! An injective real-definable coordinate map gives an original-Gamma
isomorphism from a Gamma set onto its actual image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u w : ℕ}

def gammaIso_realImage (A : Set (Point (M := M) n m)) (hA : GammaSetDefinable B A)
    (G : Map (PresentedSet.univ (pointSpace n m) B.real) (PresentedSet.univ (pointSpace u w) B.real))
    (hG : Function.Injective G) :
    GammaIso B A {q | ∃ a : A, (G ⟨a.val,Set.mem_univ _⟩).val = q} := by
  let F : A → {q | ∃ a : A, (G ⟨a.val,Set.mem_univ _⟩).val = q} :=
    fun a => ⟨(G ⟨a.val,Set.mem_univ _⟩).val,⟨a,rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      have hv := congrArg (fun y : {q | ∃ a : A, (G ⟨a.val,Set.mem_univ _⟩).val = q} => y.val) he
      have hg : G ⟨a.val,Set.mem_univ _⟩ = G ⟨b.val,Set.mem_univ _⟩ := Subtype.ext hv
      exact Subtype.ext (congrArg (fun x : PresentedSet.univ (pointSpace n m) B.real => x.val) (hG hg))
    · rintro ⟨q,a,ha⟩
      exact ⟨a,Subtype.ext ha⟩
  refine ⟨Equiv.ofBijective F hF,?_⟩
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hA ((gammaLogicInput B).real_map_graph G))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    exact (congrArg (fun x => (G x).val) (Subtype.ext ha.symm)).trans hq
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

end IntegrationInACVF.Section6
