module

public import Integration7.RVLabelChainLifts
public import Integration7.GammaRVLabelFocusLifts
public import Section5.GammaRestriction

@[expose] public section

/-! Carried-label special chains retain their complete original-Gamma
certificates at every primitive, including intermediate target domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)}
variable {S : Set M} {n a b d l : ℕ}

set_option maxHeartbeats 1600000 in
theorem gamma_chain_lift_rv_labels {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : Chain S n A B) :
    GammaChainDefinable P T →
    ∀ {l d : ℕ} (H : DefSet (M := M) S n l) (ρ : Fin a → Fin l) (χ : Fin d → Fin l)
      (hJoint : RVLabelsJointlyDetermine (M := M) ρ χ)
      (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
      (hH : GammaSetDefinable P (carrier H)) (previous : Option Bool), T.Alternating previous →
      ∃ r : ℕ, ∃ K : DefSet (M := M) S n r, ∃ σ : Fin b → Fin r, ∃ τ : Fin d → Fin r,
      ∃ W : Chain S n H K, W.Alternating previous ∧ GammaChainDefinable P W ∧ RVLabelsJointlyDetermine (M := M) σ τ ∧
        (∀ p : H, retainVFLabels σ (W.toMap p).val =
          (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).val) ∧
        ∀ p : H, (W.toMap p).val.2 ∘ τ = p.val.2 ∘ χ := by
  induction T with
  | nil A =>
    intro hT l d H ρ χ hJoint hHA hH previous _
    exact ⟨l,H,ρ,χ,.nil H,trivial,hH,hJoint,fun _ => rfl,fun _ => rfl⟩
  | @cons a' b' c' A' B' C' step tail ih =>
    intro hT
    cases step with
    | canonical =>
      intro l d H ρ χ hJoint hHA hH previous hAlt
      let H' := canonicalImage H
      let ρ' := rvLabelCanonicalProjection (n := n) ρ
      let χ' := Fin.natAdd n ∘ χ
      have hsub : ∀ p ∈ carrier H', retainVFLabels ρ' p ∈ carrier (canonicalImage A') := by
        intro p hp
        rw [canonicalImage_carrier] at hp
        obtain ⟨q,hq,rfl⟩ := hp
        rw [retain_vf_labels_canonical,canonicalImage_carrier]
        exact ⟨retainVFLabels ρ q,hHA q hq,rfl⟩
      have hH' := GammaPrimitiveDefinable.target (gammaLogicInput P) (Primitive.canonical H) hH
      obtain ⟨r,K,σ,τ,U,hU,hUΓ,hJoint',hu,hExtra⟩ := ih hT.2 H' ρ' χ'
        (rv_labels_jointly_determine_canonical ρ χ hJoint) hsub hH' (some false) hAlt.2
      let W : Chain S n H K := .cons (.canonical H) U
      refine ⟨r,K,σ,τ,W,⟨hAlt.1,hU⟩,⟨hH,hUΓ⟩,hJoint',?_,?_⟩
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
      intro l d H ρ χ hJoint hHA hH previous hAlt
      let F := rvLabelFocusLift D ρ hHA
      have hsub : ∀ p ∈ carrier F.etaImage, retainVFLabels ρ p ∈ carrier D.etaImage := by
        intro p hp
        rw [Focus.etaImage_carrier] at hp
        obtain ⟨q,hq,rfl⟩ := hp
        rw [rv_label_focus_lift_eta D ρ hHA q hq,Focus.etaImage_carrier]
        exact ⟨retainVFLabels ρ q,hHA q hq,rfl⟩
      have hFΓ := gamma_rv_label_focus_lift D ρ hHA hH hT.1.2
      have hH' := GammaPrimitiveDefinable.target (gammaLogicInput P) (Primitive.centripetal F) ⟨hH,hFΓ⟩
      obtain ⟨r,K,σ,τ,U,hU,hUΓ,hJoint',hu,hExtra⟩ := ih hT.2 F.etaImage ρ χ hJoint hsub hH' (some true) hAlt.2
      let W : Chain S n H K := .cons (.centripetal F) U
      refine ⟨r,K,σ,τ,W,⟨hAlt.1,hU⟩,⟨⟨hH,hFΓ⟩,hUΓ⟩,hJoint',?_,?_⟩
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
