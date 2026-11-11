import IntegrationSection4.FamilyPreparedLinearity
import IntegrationSection4.FamilyOpenPartition
import IntegrationSection3ACVF.AdjoinGamma

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyLinearPreparation

open GammaFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem membership_definable (G : GammaParameters.Base (M := M)) {m : ℕ}
    (W : Set (Fin m ⊕ Fin 1 → M))
    (hW : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) W) :
    GammaGraphDefinable G (fun (p : Point (M := M) 1 m) (_ : Point (M := M) 0 0) =>
      Sum.elim (labels p) (fun _ : Fin 1 => (vfAt p 0).val) ∈ W) := by
  let ρ : Fin m ⊕ Fin 1 → Fin ((1+m)+(0+0)) :=
    Sum.elim (fun i => Fin.castAdd (0+0) (Fin.natAdd 1 i))
      (fun _ => Fin.castAdd (0+0) (Fin.castAdd m (0 : Fin 1)))
  have h := GammaTupleGraphs.relation_of_full G _ (FullBaseAtomicity.OverBase.preimage_comp hW ρ)
  apply GammaGraphDefinable.congr h
  intro p q
  change (fun j => Fin.append (gammaPointCode p) (gammaPointCode q) (ρ j)) ∈ W ↔ _
  have he : (fun j => Fin.append (gammaPointCode p) (gammaPointCode q) (ρ j)) =
      Sum.elim (labels p) (fun _ : Fin 1 => (vfAt p 0).val) := by
    funext j
    cases j with
    | inl i => simp only [ρ,Sum.elim_inl,Fin.append_left,gammaPointCode,Fin.append_right]; rfl
    | inr i => simp only [ρ,Sum.elim_inr,Fin.append_left,gammaPointCode,Fin.append_left]
  rw [he]

/-- Lemma 4.2 uniformly in pre-existing RV labels. The witness is a
single actual special bijection over the original Gamma base. -/
theorem prepare {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) {m : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f)
    (hInj : ∀ p, Set.InjOn (f p) (A p)) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
    ∃ T : GammaSpecialBijection G (domain A) E,
      IsRVPullback E ∧ ∀ b : T.target,
        (∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body T.special b)
          (f (labels (T.special.inverseMap b).val))
          (fun x hx => hfVF _ x (FamilyPreparedLinearity.body_subset A T.special T.source_eq b hx)) s) ∧
        MaximalOpenClasses.OpenToOpen (InverseBodies.body T.special b)
          (f (labels (T.special.inverseMap b).val)) := by
  let B := GammaBaseBridge.fullBase G
  have hδF : FullGammaSyntax.Scalar B {δ} := AdjoinGamma.named_scalar δ ⟨δ,hδ,rfl⟩
  obtain ⟨P,hP,hCover⟩ := FamilyOpenPartition.exists_partition hκ hs B hsmall h00 δ hδF hδ1
    A hAVF f hfVF hf hInj
  have hDomain := GammaFamilySyntax.domain_definable G A (FiniteScalarFamilies.domain_definable B A f hf)
  obtain ⟨l,E,T,hE,hRows⟩ := GammaFamilySyntax.prepare hs h00 G hsmall hGenerated (domain A) hDomain
    (linearRow A f) (GammaFamilySyntax.linearRow_definable G A f hf)
  let rPiece (U : P) (p : Point (M := M) 1 m) (_ : Point (M := M) 0 0) : Prop :=
    Sum.elim (labels p) (fun _ : Fin 1 => (vfAt p 0).val) ∈ U.val
  have hrPiece (U : P) : GammaGraphDefinable G (rPiece U) :=
    membership_definable G U.val (hP U.val U.property).2.2.1
  obtain ⟨q,F,W,hWG,hF,hRef,hPrepared⟩ := FiniteRelationPreparation.prepare_finite hs h00 G hsmall
    hGenerated T.real_contains T.special T.invariant_graphs (T.target_eq.symm ▸ hE) rPiece hrPiece Finset.univ
  have hRowsW := FiniteRelationPreparation.Uniform.refine hRows hRef
  let V : GammaSpecialBijection G (domain A) (carrier F) :=
    ⟨T.codes,T.real_contains,T.source,F,T.source_eq,rfl,W,hWG⟩
  refine ⟨q,carrier F,V,hF,fun b => ⟨?_,?_⟩⟩
  · exact FamilyPreparedLinearity.linear_on_body hκ hs B hsmall h00 A f hf hfVF hInj
      W T.source_eq hF hRowsW b
  · let p := labels (W.inverseMap b).val
    let x₀ := (vfAt (W.inverseMap b).val 0).val
    have hx₀ : x₀ ∈ InverseBodies.body W b :=
      ⟨W.inverseMap b,rfl,by rw [W.apply_inverse]; rfl⟩
    have hxA := FamilyPreparedLinearity.body_subset A W T.source_eq b hx₀
    obtain ⟨U,hUP,hxU⟩ := (hCover p x₀).mp hxA
    let u : P := ⟨U,hUP⟩
    have hBodyU : InverseBodies.body W b ⊆ {x | Sum.elim p (fun _ : Fin 1 => x) ∈ U} := by
      rintro x ⟨a,ha,he⟩
      have hh := hPrepared u (Finset.mem_univ u) (W.toMap a) b he (Fin.elim0,Fin.elim0)
      rw [W.inverse_apply] at hh
      change (Sum.elim (labels a.val) (fun _ : Fin 1 => (vfAt a.val 0).val) ∈ U) ↔
        Sum.elim p (fun _ : Fin 1 => x₀) ∈ U at hh
      have hm := hh.mpr hxU
      rw [FamilyPreparedLinearity.source_labels W a b he,ha] at hm
      exact hm
    intro Q hQ
    exact (hP U hUP).2.2.2 p Q (hQ.trans hBodyU)

end IntegrationInACVF.Section4.FamilyLinearPreparation
