module

public import Integration7.FactoredRVConstraintHeadMaps

@[expose] public section

/-! Literal suffix identities for a unary preparation carrying arbitrary
functional RV labels, without any independence assumption on those labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}
variable {ρ : Fin a → Fin l}
namespace RVLabelConstraintSpecialPreparation

theorem carried_head_suffix (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (q : headImage L.target) (j : Fin l) :
    q.val.2 (L.headParameters j) =
      q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) j)) := by
  obtain ⟨v,hv⟩ := q.property
  obtain ⟨p,hp⟩ := L.special.bijective.2 v
  have he : headKey (L.special.toMap p).val=q.val :=
    (congrArg (fun z : L.target => headKey z.val) hp).trans ((headKeyMap_apply L.target v).symm.trans hv)
  change q.val.2 (Fin.natAdd 1 (L.carried j)) = _
  rw [← he]
  simp only [headKey,Fin.append_right]
  exact (congrFun (L.parameters p) j).trans (special_oldLabels L.special p j).symm

theorem prepared_head_suffix (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
    (q : headImage L.target) (j : Fin a) :
    q.val.2 (L.headProjection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) j))) =
      q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (ρ j))) :=
  (congrFun (L.head_product_map_compatible q) j).trans (L.carried_head_suffix q (ρ j))
end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
