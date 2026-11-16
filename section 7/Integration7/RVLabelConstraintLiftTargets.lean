module

public import Integration7.RVParameterLiftTargetPullbacks
public import IntegrationSection5.RelativeLabelPreservation

@[expose] public section

/-! Exact targets of special-chain lifts with shared old RV labels.
The only additional target condition is equality of the two retained
copies of those labels; hence an RV-pullback target remains one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b l r : ℕ}

set_option maxHeartbeats 1600000 in
theorem rv_label_constraint_lift_target_carrier
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (Q : DefSet (M := M) S 0 l) (ρ : Fin a → Fin l)
    (σ : Fin b → Fin r) (τ : Fin l → Fin r)
    (hSource : ∀ p : Point (M := M) n l, p ∈ carrier H ↔
      retainVFLabels ρ p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels ρ p.val,((hSource p.val).mp p.property).1⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2)
    (q : Point (M := M) n r) :
    q ∈ carrier K ↔ retainVFLabels σ q ∈ carrier B ∧
      (Fin.elim0,q.2 ∘ τ) ∈ carrier Q ∧
      (q.2 ∘ σ) ∘ suffixIndex (special_chain_rvArity_le T.chain) = (q.2 ∘ τ) ∘ ρ := by
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := W.bijective.2 ⟨q,hq⟩
    have he := congrArg Subtype.val hp
    have hCompare' := hCompare p
    rw [he] at hCompare'
    have hLabels : q.2 ∘ τ = p.val.2 :=
      (congrArg (fun z : Point (M := M) n r => z.2 ∘ τ) he).symm.trans (hExtra p)
    refine ⟨hCompare'.symm ▸ (T.toMap ⟨retainVFLabels ρ p.val,
      ((hSource p.val).mp p.property).1⟩).property,?_,?_⟩
    · rw [hLabels]
      exact ((hSource p.val).mp p.property).2
    · rw [hLabels]
      funext i
      have h := congrArg (fun z : Point (M := M) n b =>
        z.2 (suffixIndex (special_chain_rvArity_le T.chain) i)) hCompare'
      exact h.trans (special_oldLabels T _ i)
  · rintro ⟨hq,hQ,hCompatible⟩
    let a := T.inverseMap ⟨retainVFLabels σ q,hq⟩
    have haLabels : a.val.2 = (q.2 ∘ τ) ∘ ρ := by
      funext i
      have hOld := special_oldLabels T a i
      have hInv := congrArg (fun z : B => z.val.2 (suffixIndex (special_chain_rvArity_le T.chain) i))
        (T.apply_inverse ⟨retainVFLabels σ q,hq⟩)
      exact hOld.symm.trans (hInv.trans (congrFun hCompatible i))
    let p0 : Point (M := M) n l := (a.val.1,q.2 ∘ τ)
    have hP0 : retainVFLabels ρ p0 = a.val := Prod.ext rfl haLabels.symm
    let p : H := ⟨p0,(hSource p0).mpr ⟨hP0.symm ▸ a.property,hQ⟩⟩
    have ha : (⟨retainVFLabels ρ p.val,((hSource p.val).mp p.property).1⟩ : A) = a := Subtype.ext hP0
    have hProjected : retainVFLabels σ (W.toMap p).val = retainVFLabels σ q := by
      rw [hCompare p,ha,T.apply_inverse]
    have hVF := congrArg Prod.fst hProjected
    have hRV := hJoint (W.toMap p).val.2 q.2 (congrArg Prod.snd hProjected) (hExtra p)
    have he : (W.toMap p).val = q := Prod.ext hVF hRV
    exact he ▸ (W.toMap p).property

theorem rv_label_constraint_lift_target_pullback
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (Q : DefSet (M := M) S 0 l) (ρ : Fin a → Fin l)
    (σ : Fin b → Fin r) (τ : Fin l → Fin r)
    (hSource : ∀ p : Point (M := M) n l, p ∈ carrier H ↔
      retainVFLabels ρ p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels ρ p.val,((hSource p.val).mp p.property).1⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2)
    (hB : IsRVPullback (carrier B)) : IsRVPullback (carrier K) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hP := (rv_label_constraint_lift_target_carrier T W Q ρ σ τ hSource hJoint hCompare hExtra p).mp hp
  apply (rv_label_constraint_lift_target_carrier T W Q ρ σ τ hSource hJoint hCompare hExtra q).mpr
  have hLabels := ((sameRV_iff _ _).mp he).2
  refine ⟨(isRVPullback_iff _).mp hB _ hP.1 _ (same_rv_retain_vf_labels σ he),?_,?_⟩
  · exact (congrArg (fun z : Fin l → RV (M := M) => (Fin.elim0,z) ∈ carrier Q)
      (congrArg (fun z => z ∘ τ) hLabels)).mp hP.2.1
  · rw [← hLabels]
    exact hP.2.2

end IntegrationInACVF.Section7
