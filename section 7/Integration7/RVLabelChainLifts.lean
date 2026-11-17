module

public import Integration7.RVLabelFocusLifts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual alternating special chains lift while carrying extra RV
labels. The projected old labels together with the carried labels still
determine the entire output tuple; the extra labels are unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b d l : ℕ}

def RVLabelsJointlyDetermine (ρ : Fin a → Fin l) (χ : Fin d → Fin l) : Prop :=
  ∀ x y : Fin l → RV (M := M), x ∘ ρ = y ∘ ρ → x ∘ χ = y ∘ χ → x = y

theorem rv_labels_jointly_determine_canonical (ρ : Fin a → Fin l) (χ : Fin d → Fin l)
    (h : RVLabelsJointlyDetermine (M := M) ρ χ) :
    RVLabelsJointlyDetermine (M := M) (rvLabelCanonicalProjection (n := n) ρ) (Fin.natAdd n ∘ χ) := by
  intro x y hρ hχ
  have hTail : x ∘ Fin.natAdd n = y ∘ Fin.natAdd n := by
    apply h
    · funext j
      have he := congrFun hρ (Fin.natAdd n j)
      simpa only [Function.comp_apply,rvLabelCanonicalProjection,Fin.addCases_right] using he
    · exact hχ
  funext j
  cases j using Fin.addCases with
  | left i =>
    have he := congrFun hρ (Fin.castAdd a i)
    simpa only [Function.comp_apply,rvLabelCanonicalProjection,Fin.addCases_left] using he
  | right i => exact congrFun hTail i

set_option maxHeartbeats 1600000 in
theorem chain_lift_rv_labels {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : Chain S n A B) :
    ∀ {l d : ℕ} (H : DefSet (M := M) S n l) (ρ : Fin a → Fin l) (χ : Fin d → Fin l)
      (hJoint : RVLabelsJointlyDetermine (M := M) ρ χ)
      (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
      (previous : Option Bool), T.Alternating previous →
      ∃ r : ℕ, ∃ K : DefSet (M := M) S n r, ∃ σ : Fin b → Fin r, ∃ τ : Fin d → Fin r,
      ∃ W : Chain S n H K, W.Alternating previous ∧ RVLabelsJointlyDetermine (M := M) σ τ ∧
        (∀ p : H, retainVFLabels σ (W.toMap p).val =
          (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).val) ∧
        ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2 ∘ χ := by
  induction T with
  | nil A =>
    intro l d H ρ χ hJoint hHA previous _
    exact ⟨l,H,ρ,χ,.nil H,trivial,hJoint,fun _ => rfl,fun _ => rfl⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    cases step with
    | canonical =>
      intro l d H ρ χ hJoint hHA previous hAlt
      let H' := canonicalImage H
      let ρ' := rvLabelCanonicalProjection (n := n) ρ
      let χ' := Fin.natAdd n ∘ χ
      have hsub : ∀ p ∈ carrier H', retainVFLabels ρ' p ∈ carrier (canonicalImage A') := by
        intro p hp
        rw [canonicalImage_carrier] at hp
        obtain ⟨q,hq,rfl⟩ := hp
        rw [retain_vf_labels_canonical,canonicalImage_carrier]
        exact ⟨retainVFLabels ρ q,hHA q hq,rfl⟩
      obtain ⟨r,K,σ,τ,U,hU,hJoint',hu,hExtra⟩ := ih H' ρ' χ'
        (rv_labels_jointly_determine_canonical ρ χ hJoint) hsub (some false) hAlt.2
      let W : Chain S n H K := .cons (.canonical H) U
      refine ⟨r,K,σ,τ,W,⟨hAlt.1,hU⟩,hJoint',?_,?_⟩
      · intro p
        change retainVFLabels σ (U.toMap ((SpecialBijection.canonical H).toMap p)).val = _
        rw [hu]
        have he : (⟨retainVFLabels ρ' ((SpecialBijection.canonical H).toMap p).val,
            hsub _ ((SpecialBijection.canonical H).toMap p).property⟩ : canonicalImage A') =
            (SpecialBijection.canonical A').toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩ := by
          apply Subtype.ext
          exact retain_vf_labels_canonical ρ p.val
        rw [he]
        rfl
      · intro p
        exact (hExtra ((SpecialBijection.canonical H).toMap p)).trans (by
          funext j
          change (canonical p.val).2 (Fin.natAdd n (χ j)) = p.val.2 (χ j)
          exact Fin.append_right (fun i : Fin n => rv (vfAt p.val i)) p.val.2 (χ j))
    | centripetal D =>
      intro l d H ρ χ hJoint hHA previous hAlt
      let F := rvLabelFocusLift D ρ hHA
      have hsub : ∀ p ∈ carrier F.etaImage, retainVFLabels ρ p ∈ carrier D.etaImage := by
        intro p hp
        rw [Focus.etaImage_carrier] at hp
        obtain ⟨q,hq,rfl⟩ := hp
        rw [rv_label_focus_lift_eta D ρ hHA q hq,Focus.etaImage_carrier]
        exact ⟨retainVFLabels ρ q,hHA q hq,rfl⟩
      obtain ⟨r,K,σ,τ,U,hU,hJoint',hu,hExtra⟩ := ih F.etaImage ρ χ hJoint hsub (some true) hAlt.2
      let W : Chain S n H K := .cons (.centripetal F) U
      refine ⟨r,K,σ,τ,W,⟨hAlt.1,hU⟩,hJoint',?_,?_⟩
      · intro p
        change retainVFLabels σ (U.toMap ((SpecialBijection.centripetal F).toMap p)).val = _
        rw [hu]
        have he : (⟨retainVFLabels ρ ((SpecialBijection.centripetal F).toMap p).val,
            hsub _ ((SpecialBijection.centripetal F).toMap p).property⟩ : D.etaImage) =
            (SpecialBijection.centripetal D).toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩ := by
          apply Subtype.ext
          exact rv_label_focus_lift_eta D ρ hHA p.val p.property
        rw [he]
        rfl
      · intro p
        exact (hExtra ((SpecialBijection.centripetal F).toMap p)).trans
          (congrArg (fun r => r ∘ χ) (F.toFocusGeometry.eta_labels p.val))

end IntegrationInACVF.Section7
