module

public import Integration7.PureRVLabelGraphFactorizations

@[expose] public section

/-! Membership in a pure-RV label graph keeps both the original tuple
and the actual value of the appended definable map explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {l e : ℕ}

theorem mem_pure_rv_label_graph (Q : DefSet (M := M) S 0 l)
    (g : Map Q (PresentedSet.univ (pointSpace (M := M) 0 e) S)) (p : Point (M := M) 0 (l+e)) :
    p ∈ carrier (pureRVLabelGraph Q g) ↔
      ∃ q : Q, q.val=(Fin.elim0,p.2 ∘ Fin.castAdd e) ∧ (g q).val.2=p.2 ∘ Fin.natAdd l := by
  constructor
  · rintro ⟨q,hq⟩
    change (Fin.elim0,Fin.append q.val.2 (g q).val.2)=p at hq
    refine ⟨q,Prod.ext (Subsingleton.elim _ _) ?_,?_⟩
    · funext i
      exact (Fin.append_left _ _ i).symm.trans (congrArg (fun w => w.2 (Fin.castAdd e i)) hq)
    · funext i
      exact (Fin.append_right _ _ i).symm.trans (congrArg (fun w => w.2 (Fin.natAdd l i)) hq)
  · rintro ⟨q,hq,hg⟩
    refine ⟨q,?_⟩
    change (Fin.elim0,Fin.append q.val.2 (g q).val.2)=p
    apply Prod.ext (Subsingleton.elim _ _)
    rw [congrArg Prod.snd hq,hg]
    exact Fin.append_castAdd_natAdd
end IntegrationInACVF.Section7
