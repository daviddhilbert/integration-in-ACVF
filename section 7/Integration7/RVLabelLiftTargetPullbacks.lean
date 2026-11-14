import Integration7.RVLabelChainLifts

/-! Exact target geometry of carried-label special lifts. A surjective
source projection with constant extra labels yields precisely the
original target with those same extra labels, and hence an RV-pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b l r d : ℕ}

theorem rv_label_lift_target_carrier
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (ρ : Fin a → Fin l) (χ : Fin d → Fin l) (σ : Fin b → Fin r) (τ : Fin d → Fin r)
    (t : Fin d → RV (M := M))
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
    (hSurj : ∀ a : A, ∃ p : H, retainVFLabels ρ p.val = a.val)
    (hSource : ∀ p : H, p.val.2 ∘ χ = t)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2 ∘ χ)
    (q : Point (M := M) n r) :
    q ∈ carrier K ↔ retainVFLabels σ q ∈ carrier B ∧ q.2 ∘ τ = t := by
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := W.bijective.2 ⟨q,hq⟩
    have he : (W.toMap p).val = q := congrArg Subtype.val hp
    refine ⟨?_,?_⟩
    · have hh := hCompare p
      rw [he] at hh
      exact hh.symm ▸ (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).property
    · exact (congrArg (fun z => z.2 ∘ τ) he).symm.trans ((hExtra p).trans (hSource p))
  · rintro ⟨hq,hqt⟩
    let b : B := ⟨retainVFLabels σ q,hq⟩
    let a := T.inverseMap b
    obtain ⟨p,hp⟩ := hSurj a
    have ha : (⟨retainVFLabels ρ p.val,hHA p.val p.property⟩ : A) = a := Subtype.ext hp
    have hProjected : retainVFLabels σ (W.toMap p).val = retainVFLabels σ q := by
      rw [hCompare p,ha,T.apply_inverse]
    have hVF := congrArg Prod.fst hProjected
    have hRV := hJoint (W.toMap p).val.2 q.2 (congrArg Prod.snd hProjected)
      ((hExtra p).trans ((hSource p).trans hqt.symm))
    have he : (W.toMap p).val = q := Prod.ext hVF hRV
    exact he ▸ (W.toMap p).property

theorem rv_label_lift_target_pullback
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (ρ : Fin a → Fin l) (χ : Fin d → Fin l) (σ : Fin b → Fin r) (τ : Fin d → Fin r)
    (t : Fin d → RV (M := M))
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
    (hSurj : ∀ a : A, ∃ p : H, retainVFLabels ρ p.val = a.val)
    (hSource : ∀ p : H, p.val.2 ∘ χ = t)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2 ∘ χ)
    (hB : IsRVPullback (carrier B)) : IsRVPullback (carrier K) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hP := (rv_label_lift_target_carrier T W ρ χ σ τ t hHA hSurj hSource hJoint hCompare hExtra p).mp hp
  apply (rv_label_lift_target_carrier T W ρ χ σ τ t hHA hSurj hSource hJoint hCompare hExtra q).mpr
  refine ⟨(isRVPullback_iff _).mp hB _ hP.1 _ (same_rv_retain_vf_labels σ he),?_⟩
  exact (congrArg (fun x => x ∘ τ) ((sameRV_iff _ _).mp he).2).symm.trans hP.2

end IntegrationInACVF.Section7
