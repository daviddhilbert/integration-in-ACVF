import Integration7.HeadCoordinateFibrePreparation
import IntegrationSection6.StandardProgramPresentations

/-! The frozen fibre of an actual head preparation gives a unary standard
contraction. Its final RV labels are exactly the original head fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

def headCoordinateFibreContraction (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    StandardContraction (coordinateFibre U 0 (headFrozenTuple x)) (Equiv.refl _) :=
  standardFromProgram _ _ (.step (headCoordinateFibrePreparation T x) (.zero _))
    (vfPermutationImage_id_eq _).symm

theorem gamma_head_coordinate_fibre_contraction (T : HeadPreparation U)
    (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaProgramDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (headCoordinateFibreContraction T x).program := by
  apply gamma_standardFromProgram
  exact ⟨gamma_head_coordinate_fibre_preparation_map T hT x,
    gamma_head_coordinate_fibre_preparation_target T hTarget x,
    gamma_headImage _ (gamma_head_coordinate_fibre_preparation_target T hTarget x)⟩

theorem head_coordinate_fibre_contraction_domain (T : HeadPreparation U)
    (x : Fin n → VF (M := M)) (r : Fin (1+T.arity) → RV (M := M)) :
    (Fin.elim0,r) ∈ carrier (headCoordinateFibreContraction T x).target ↔
      (x,r) ∈ carrier T.contractedSet := by
  change (Fin.elim0,r) ∈ carrier (headImage (coordinateFibre T.target 0 (headFrozenTuple x))) ↔
    (x,r) ∈ carrier (headImage T.target)
  rw [headImage_carrier,headImage_carrier]
  constructor
  · rintro ⟨q,hq,he⟩
    refine ⟨coordinateInsert 0 (headFrozenTuple x) q,hq,?_⟩
    rw [coordinateInsert_head]
    have hr : (headKey q).2 = r := congrArg Prod.snd he
    exact Prod.ext rfl hr
  · rintro ⟨q,hq,he⟩
    have hTail : (fun j => q.1 j.succ) = x := congrArg Prod.fst he
    let p : Point (M := M) 1 T.arity := (fun _ => q.1 0,q.2)
    have hp : coordinateInsert 0 (headFrozenTuple x) p = q := by
      rw [coordinateInsert_head]
      refine Prod.ext ?_ rfl
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact (congrFun hTail j).symm
    have hr : (headKey q).2 = r := congrArg Prod.snd he
    refine ⟨p,?_,Prod.ext (Subsingleton.elim _ _) hr⟩
    change coordinateInsert 0 (headFrozenTuple x) p ∈ carrier T.target
    rwa [hp]

end IntegrationInACVF.Section7
