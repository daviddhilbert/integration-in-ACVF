module

public import Integration7.IndependentRVConstraintHeadMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The independent head product retains the literal original labels.
The carried tuple agrees with the old suffix, and the prepared unary
factor recovers precisely the original first block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b d : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 (a+d)} {Q : DefSet (M := M) S 0 (a+d)}
namespace RVLabelConstraintSpecialPreparation

theorem head_carried_eq_old_suffix (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (q : headImage L.target) (j : Fin (a+d)) :
    q.val.2 (L.headParameters j) =
      q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) j)) := by
  obtain ⟨v,hv⟩ := q.property
  obtain ⟨p,hp⟩ := L.special.bijective.2 v
  have he : headKey (L.special.toMap p).val = q.val :=
    (congrArg (fun z : L.target => headKey z.val) hp).trans ((headKeyMap_apply L.target v).symm.trans hv)
  change q.val.2 (Fin.natAdd 1 (L.carried j)) = _
  rw [← he]
  simp only [headKey,Fin.append_right]
  exact (congrFun (L.parameters p) j).trans (special_oldLabels L.special p j).symm

theorem head_prepared_old_labels (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (q : headImage L.target) (j : Fin a) :
    q.val.2 (L.headProjection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) j))) =
      q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.castAdd d j))) :=
  (congrFun (L.head_product_map_compatible q) j).trans (L.head_carried_eq_old_suffix q (Fin.castAdd d j))

theorem head_coefficient_old_labels (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
    (q : headImage L.target) (j : Fin d) :
    q.val.2 (L.headParameters (Fin.natAdd a j)) =
      q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.natAdd a j))) :=
  L.head_carried_eq_old_suffix q (Fin.natAdd a j)
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
