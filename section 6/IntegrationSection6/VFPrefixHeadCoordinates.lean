import IntegrationSection6.VFPrefixCoordinates
import IntegrationSection5.HeadPreparation

/-! Prefix freezing commutes with head-coordinate fibres and deletion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n p m : ℕ}

theorem vfPrefixInsert_coordinateInsert (x : Fin n → VF (M := M))
    (u : Fin (p+1) → VF (M := M)) (q : Point (M := M) 1 m) :
    vfPrefixInsert (p := p+1) x (coordinateInsert 0 u q) = coordinateInsert 0 (vfPrefixTuple x u) q := by
  refine Prod.ext ?_ rfl
  have h := congrArg (fun r : Point (M := M) (n+(p+1)) 0 => r.1)
    (vfPrefixInsert_replace x ((u,Fin.elim0) : Point (M := M) (p+1) 0) (vfAt q 0))
  exact h

theorem vfPrefixInsert_dropHead (x : Fin n → VF (M := M))
    (q : Point (M := M) (p+1) m) :
    vfPrefixInsert (p := p) x (dropHead id q) = dropHead (n := n+p) id (vfPrefixInsert (p := p+1) x q) := by
  refine Prod.ext ?_ rfl
  have h := vfPrefixTuple_cons x q.1
  funext j
  exact (congrFun h j.succ).symm

theorem vfPrefixInsert_headKey (x : Fin n → VF (M := M))
    (q : Point (M := M) (p+1) m) :
    vfPrefixInsert (p := p) x (headKey q) = headKey (n := n+p) (vfPrefixInsert (p := p+1) x q) := by
  refine Prod.ext ?_ ?_
  · have h := vfPrefixTuple_cons x q.1
    funext j
    exact (congrFun h j.succ).symm
  · change Fin.append (fun _ : Fin 1 => @rv M sM hM (vfAt q 0)) q.2 =
      Fin.append (fun _ : Fin 1 => @rv M sM hM (vfPrefixTuple x q.1 0)) q.2
    exact congrArg (fun z => Fin.append (fun _ : Fin 1 => @rv M sM hM z) q.2)
      (vfPrefixTuple_head x q.1 0).symm

end IntegrationInACVF.Section6
