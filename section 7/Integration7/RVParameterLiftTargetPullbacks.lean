module

public import Integration7.RVLabelChainLifts

@[expose] public section

/-! A special preparation of a pure VF domain lifts over an arbitrary
RV parameter domain. The exact target is the old target with those carried
parameters, so an RV-pullback target stays an RV-pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n b l r : ℕ}

theorem rv_parameter_lift_target_carrier
    {A : DefSet (M := M) S n 0} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (Q : DefSet (M := M) S 0 l) (σ : Fin b → Fin r) (τ : Fin l → Fin r)
    (hSource : ∀ p : Point (M := M) n l, p ∈ carrier H ↔
      retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,((hSource p.val).mp p.property).1⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2)
    (q : Point (M := M) n r) :
    q ∈ carrier K ↔ retainVFLabels σ q ∈ carrier B ∧ (Fin.elim0,q.2 ∘ τ) ∈ carrier Q := by
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := W.bijective.2 ⟨q,hq⟩
    have he := congrArg Subtype.val hp
    refine ⟨?_,?_⟩
    · have hh := hCompare p
      rw [he] at hh
      exact hh.symm ▸ (T.toMap ⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,
        ((hSource p.val).mp p.property).1⟩).property
    · have hLabels : q.2 ∘ τ = p.val.2 :=
        (congrArg (fun z : Point (M := M) n r => z.2 ∘ τ) he).symm.trans (hExtra p)
      rw [hLabels]
      exact ((hSource p.val).mp p.property).2
  · rintro ⟨hq,hQ⟩
    let a := T.inverseMap ⟨retainVFLabels σ q,hq⟩
    let p0 : Point (M := M) n l := (a.val.1,q.2 ∘ τ)
    have hP0 : retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p0 = a.val :=
      Prod.ext rfl (Subsingleton.elim _ _)
    let p : H := ⟨p0,(hSource p0).mpr ⟨hP0.symm ▸ a.property,hQ⟩⟩
    have ha : (⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,
        ((hSource p.val).mp p.property).1⟩ : A) = a := Subtype.ext hP0
    have hProjected : retainVFLabels σ (W.toMap p).val = retainVFLabels σ q := by
      rw [hCompare p,ha,T.apply_inverse]
    have hVF := congrArg Prod.fst hProjected
    have hRV := hJoint (W.toMap p).val.2 q.2 (congrArg Prod.snd hProjected) (hExtra p)
    have he : (W.toMap p).val = q := Prod.ext hVF hRV
    exact he ▸ (W.toMap p).property

theorem rv_parameter_lift_target_pullback
    {A : DefSet (M := M) S n 0} {B : DefSet (M := M) S n b}
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (T : SpecialBijection A B) (W : SpecialBijection H K)
    (Q : DefSet (M := M) S 0 l) (σ : Fin b → Fin r) (τ : Fin l → Fin r)
    (hSource : ∀ p : Point (M := M) n l, p ∈ carrier H ↔
      retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q)
    (hJoint : RVLabelsJointlyDetermine (M := M) σ τ)
    (hCompare : ∀ p : H, retainVFLabels σ (W.toMap p).val =
      (T.toMap ⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,((hSource p.val).mp p.property).1⟩).val)
    (hExtra : ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2)
    (hB : IsRVPullback (carrier B)) : IsRVPullback (carrier K) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  have hP := (rv_parameter_lift_target_carrier T W Q σ τ hSource hJoint hCompare hExtra p).mp hp
  apply (rv_parameter_lift_target_carrier T W Q σ τ hSource hJoint hCompare hExtra q).mpr
  refine ⟨(isRVPullback_iff _).mp hB _ hP.1 _ (same_rv_retain_vf_labels σ he),?_⟩
  have hLabels := congrArg (fun z => z ∘ τ) ((sameRV_iff _ _).mp he).2
  exact (congrArg (fun z : Fin l → RV (M := M) => (Fin.elim0,z) ∈ carrier Q) hLabels).mp hP.2

end IntegrationInACVF.Section7
