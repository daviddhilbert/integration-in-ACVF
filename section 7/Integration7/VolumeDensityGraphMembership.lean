import Integration7.VolumeDensityGraphs

/-! Membership in the actual density graph, expressed using its retained
old labels and final density label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a : ℕ}

theorem mem_volume_density_graph {A : DefSet (rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (p : (rawMixedSpace (M := M) n (a+1)).Carrier) :
    p ∈ (volumeDensityGraph ω).carrier ↔
      ∃ q : A, q.val=(p.1,p.2 ∘ Fin.castAdd 1) ∧ ω.value q=p.2 (Fin.last a) := by
  constructor
  · rintro ⟨q,hq⟩
    change (q.val.1,Fin.append q.val.2 (ω.map q).val)=p at hq
    have hx : q.val.1=p.1 := congrArg (fun w => w.1) hq
    refine ⟨q,Prod.ext hx ?_,?_⟩
    · funext i
      exact (Fin.append_left _ _ i).symm.trans (congrArg (fun w => w.2 (Fin.castAdd 1 i)) hq)
    · exact (Fin.append_right q.val.2 (ω.map q).val (0 : Fin 1)).symm.trans
        (congrArg (fun w => w.2 (Fin.last a)) hq)
  · rintro ⟨q,hq,hω⟩
    refine ⟨q,?_⟩
    change (q.val.1,Fin.append q.val.2 (ω.map q).val)=p
    have hx : q.val.1=p.1 := congrArg Prod.fst hq
    apply Prod.ext hx
    have hr := congrArg Prod.snd hq
    funext i
    exact Fin.addCases (m := a) (n := 1)
      (fun j => (Fin.append_left _ _ j).trans (congrFun hr j))
      (fun j => by
        have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
        subst j
        exact (Fin.append_right _ _ 0).trans hω) i
end IntegrationInACVF.Section7
