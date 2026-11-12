import Section5.GammaLift
import Section5.GammaInvariantLogic
import Mathlib.Logic.Equiv.Set

/-! Definable gluing of two original-Gamma isomorphisms along disjoint
mixed subsets. The complete graph is their union. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u w : ℕ}

def gammaIso_disjointUnion {A D : Set (Point (M := M) n m)} {C E : Set (Point (M := M) u w)}
    (e : GammaIso B A C) (f : GammaIso B D E) (hAD : Disjoint A D) (hCE : Disjoint C E) :
    GammaIso B (A ∪ D) (C ∪ E) := by
  classical
  let F := (Equiv.Set.union hAD).trans ((Equiv.sumCongr e.equiv f.equiv).trans (Equiv.Set.union hCE).symm)
  have hLeft (x : (A ∪ D : Set (Point (M := M) n m))) (hx : x.val ∈ A) : (F x).val = (e.equiv ⟨x.val,hx⟩).val := by
    simp only [F,Equiv.trans_apply,Equiv.Set.union_apply_left hAD hx,
      Equiv.sumCongr_apply,Sum.map_inl,Equiv.Set.union_symm_apply_left]
  have hRight (x : (A ∪ D : Set (Point (M := M) n m))) (hx : x.val ∈ D) : (F x).val = (f.equiv ⟨x.val,hx⟩).val := by
    simp only [F,Equiv.trans_apply,Equiv.Set.union_apply_right hAD hx,
      Equiv.sumCongr_apply,Sum.map_inr,Equiv.Set.union_symm_apply_right]
  refine ⟨F,?_⟩
  apply GammaGraphDefinable.congr ((gammaLogicInput B).union_graph e.graph f.graph)
  intro p q
  constructor
  · rintro (⟨a,ha,hq⟩ | ⟨a,ha,hq⟩)
    · exact ⟨⟨a.val,Or.inl a.property⟩,ha,(hLeft _ a.property).trans hq⟩
    · exact ⟨⟨a.val,Or.inr a.property⟩,ha,(hRight _ a.property).trans hq⟩
  · rintro ⟨x,hx,hq⟩
    rcases x.property with hA | hD
    · exact Or.inl ⟨⟨x.val,hA⟩,hx,(hLeft x hA).symm.trans hq⟩
    · exact Or.inr ⟨⟨x.val,hD⟩,hx,(hRight x hD).symm.trans hq⟩

end IntegrationInACVF.Section6
