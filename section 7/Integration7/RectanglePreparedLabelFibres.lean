module

public import Integration7.PreparedKeyLabelSpecialPreparations
public import Integration7.RectangleFamilyPreparedTargetCarriers

@[expose] public section

/-! A prepared rectangle retains RV-fibre determination by its old
family labels when the other VF coordinate already has a fixed RV tag.
Recorded-key lifts also satisfy this property with their canonical
old-label suffix, independently of the chosen carried selector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

namespace PreparedKeyLabelSpecialPreparation
variable {G : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l}
variable {ρ : Fin a → Fin l} {ξ : Fin (1+b) → Fin l}
variable {hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A}

theorem carried_eq_suffix (L : PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G) (p : L.target) :
    p.val.2 ∘ L.carried = p.val.2 ∘ suffixIndex (special_chain_rvArity_le L.special.chain) := by
  obtain ⟨a,rfl⟩ := L.special.bijective.2 p
  funext i
  exact (congrFun (L.parameters a) i).trans (special_oldLabels L.special a i).symm

theorem suffix_labels_determine (L : PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G)
    (p q : L.target)
    (he : p.val.2 ∘ suffixIndex (special_chain_rvArity_le L.special.chain) =
      q.val.2 ∘ suffixIndex (special_chain_rvArity_le L.special.chain)) : SameRV p.val q.val :=
  L.shared_labels_determine p q ((L.carried_eq_suffix p).trans (he.trans (L.carried_eq_suffix q).symm))

end PreparedKeyLabelSpecialPreparation

set_option maxHeartbeats 1600000 in
theorem rectangle_family_prepared_labels_determine {S : Set M} {m r : ℕ}
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D))
    (hTag : ∀ p q : H, p.val.2 = q.val.2 → rv (vfAt p.val 1) = rv (vfAt q.val 1))
    (hHead : ∀ p q : D,
      p.val.2 ∘ suffixIndex (special_chain_rvArity_le T.chain) =
        q.val.2 ∘ suffixIndex (special_chain_rvArity_le T.chain) → SameRV p.val q.val)
    (p q : (rectangleFamilyHeadPreparation H hRect T hD).target)
    (he : p.val.2 ∘ suffixIndex (special_chain_rvArity_le T.chain) =
      q.val.2 ∘ suffixIndex (special_chain_rvArity_le T.chain)) : SameRV p.val q.val := by
  let R := rectangleFamilyHeadPreparation H hRect T hD
  have hp : coordinateProject 0 p.val ∈ carrier D :=
    ((rectangle_family_prepared_target_carrier H hRect T hD p.val).mp p.property).1
  have hq : coordinateProject 0 q.val ∈ carrier D :=
    ((rectangle_family_prepared_target_carrier H hRect T hD q.val).mp q.property).1
  have hSame := (sameRV_iff _ _).mp (hHead ⟨coordinateProject 0 p.val,hp⟩ ⟨coordinateProject 0 q.val,hq⟩ he)
  obtain ⟨a,ha⟩ := R.bijective.2 p
  obtain ⟨b,hb⟩ := R.bijective.2 q
  have hOld : a.val.2 = b.val.2 := by
    funext i
    have haOld := (congrArg (fun p : R.target => p.val.2 (suffixIndex (special_chain_rvArity_le T.chain) i)) ha).symm.trans
      (specialRelative_oldLabels R.special a i)
    have hbOld := (congrArg (fun p : R.target => p.val.2 (suffixIndex (special_chain_rvArity_le T.chain) i)) hb).symm.trans
      (specialRelative_oldLabels R.special b i)
    exact haOld.symm.trans ((congrFun he i).trans hbOld)
  have hpTail := (congrArg (fun p : R.target => vfAt p.val 1) ha).symm.trans
    (rectangle_family_prepared_tail H hRect T hD a)
  have hqTail := (congrArg (fun p : R.target => vfAt p.val 1) hb).symm.trans
    (rectangle_family_prepared_tail H hRect T hD b)
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,hSame.2⟩
  intro i
  fin_cases i
  · exact hSame.1 0
  · exact (congrArg rv hpTail).trans ((hTag a b hOld).trans (congrArg rv hqTail).symm)

end IntegrationInACVF.Section7
