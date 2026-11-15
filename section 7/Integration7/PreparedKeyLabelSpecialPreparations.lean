import Integration7.GammaRVLabelChainLifts
import Integration7.UniformPreparedPairKeys

/-! Lift a special preparation while carrying a recorded copy of its
entire prepared key. The carried labels determine all RV fibres of the
lifted target. Complete source inverse fibres give an actual RV pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}

structure PreparedKeyLabelSpecialPreparation
    (T : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (ρ : Fin a → Fin l) (ξ : Fin (1+b) → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A) (G : Base (M := M)) where
  arity : ℕ
  target : DefSet (M := M) S 1 arity
  projection : Fin b → Fin arity
  carried : Fin l → Fin arity
  special : SpecialBijection H target
  gamma : GammaChainDefinable G special.chain
  jointly_determine : RVLabelsJointlyDetermine (M := M) projection carried
  commutes : ∀ p : H, retainVFLabels projection (special.toMap p).val =
    (T.toMap ⟨retainVFLabels ρ p.val,hHA p.val p.property⟩).val
  parameters : ∀ p : H, (special.toMap p).val.2 ∘ carried = p.val.2
  recorded_key : ∀ q : target,
    Fin.append (fun i : Fin 1 => rv (vfAt q.val i)) (q.val.2 ∘ projection) =
      (q.val.2 ∘ carried) ∘ ξ

theorem prepared_key_label_special_preparation_exists
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain)
    (H : DefSet (M := M) S 1 l) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin a → Fin l) (ξ : Fin (1+b) → Fin l)
    (hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A)
    (hRecord : ∀ p : H,
      Fin.append (fun i : Fin 1 => rv (vfAt (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).val i))
        (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).val.2 = p.val.2 ∘ ξ) :
    Nonempty (PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G) := by
  have hJoint : RVLabelsJointlyDetermine (M := M) ρ (id : Fin l → Fin l) := fun _ _ _ h => h
  obtain ⟨r,K,σ,τ,W,hAlt,hW,hJoint',hCompare,hExtra⟩ := gamma_chain_lift_rv_labels T.chain hT
    H ρ id hJoint hHA hH none T.alternating
  let V : SpecialBijection H K := ⟨W,hAlt⟩
  refine ⟨⟨r,K,σ,τ,V,hW,hJoint',hCompare,hExtra,?_⟩⟩
  intro q
  obtain ⟨p,rfl⟩ := V.bijective.2 q
  have hKey := congrArg (fun z : Point (M := M) 1 b =>
    Fin.append (fun i : Fin 1 => rv (vfAt z i)) z.2) (hCompare p)
  exact hKey.trans ((hRecord p).trans (congrArg (fun t => t ∘ ξ) (hExtra p)).symm)

namespace PreparedKeyLabelSpecialPreparation
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l}
variable {ρ : Fin a → Fin l} {ξ : Fin (1+b) → Fin l}
variable {hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A}

theorem shared_labels_determine (L : PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G)
    (p q : L.target) (he : p.val.2 ∘ L.carried = q.val.2 ∘ L.carried) : SameRV p.val q.val := by
  have hKey := (L.recorded_key p).trans ((congrArg (fun t => t ∘ ξ) he).trans (L.recorded_key q).symm)
  have hSame := (flattened_key_eq_iff_same_rv (retainVFLabels L.projection p.val)
    (retainVFLabels L.projection q.val)).mp hKey
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp hSame
  exact (sameRV_iff _ _).mpr ⟨hVF,L.jointly_determine p.val.2 q.val.2 hRV he⟩

set_option maxHeartbeats 1800000 in
theorem target_pullback (L : PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G)
    (hB : IsRVPullback (carrier B))
    (hWhole : ∀ p : H, ∀ u : A,
      SameRV (T.toMap u).val (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).val →
        (u.val.1,p.val.2) ∈ carrier H) : IsRVPullback (carrier L.target) := by
  apply (isRVPullback_iff _).mpr
  intro q hq z he
  obtain ⟨p,hp⟩ := L.special.bijective.2 ⟨q,hq⟩
  have hpVal := congrArg Subtype.val hp
  have hCompare := L.commutes p
  rw [hpVal] at hCompare
  have hQ : retainVFLabels L.projection q ∈ carrier B :=
    Eq.mp (congrArg (fun w : Point (M := M) 1 b => w ∈ carrier B) hCompare.symm)
      (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).property
  have hZ : retainVFLabels L.projection z ∈ carrier B :=
    (isRVPullback_iff _).mp hB _ hQ _ (same_rv_retain_vf_labels L.projection he)
  let v : B := ⟨retainVFLabels L.projection z,hZ⟩
  let u := T.inverseMap v
  have hTu : (T.toMap u).val = retainVFLabels L.projection z := congrArg Subtype.val (T.apply_inverse v)
  have hSame : SameRV (T.toMap u).val (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).val := by
    rw [hTu,← hCompare]
    exact same_rv_retain_vf_labels L.projection he.symm
  have huLabels := ((sameRV_iff _ _).mp (T.inverse_contractible _ _ hSame)).2
  rw [T.inverse_apply,T.inverse_apply] at huLabels
  let p₀ : H := ⟨(u.val.1,p.val.2),hWhole p u hSame⟩
  have hSource : (⟨retainVFLabels ρ p₀.val,hHA _ p₀.property⟩ : A) = u := by
    apply Subtype.ext
    exact Prod.ext rfl huLabels.symm
  have hProjected : retainVFLabels L.projection (L.special.toMap p₀).val =
      retainVFLabels L.projection z := by
    rw [L.commutes p₀,hSource]
    exact hTu
  have hCarriedQ : q.2 ∘ L.carried = p.val.2 :=
    (congrArg (fun w : Point (M := M) 1 L.arity => w.2 ∘ L.carried) hpVal).symm.trans (L.parameters p)
  have hCarried : (L.special.toMap p₀).val.2 ∘ L.carried = z.2 ∘ L.carried := by
    have hLabels := ((sameRV_iff _ _).mp he).2
    exact (L.parameters p₀).trans (hCarriedQ.symm.trans (congrArg (fun t => t ∘ L.carried) hLabels))
  have hVF := congrArg Prod.fst hProjected
  have hValue : (L.special.toMap p₀).val = z := Prod.ext hVF
    (L.jointly_determine _ _ (congrArg Prod.snd hProjected) hCarried)
  exact Eq.mp (congrArg (fun w : Point (M := M) 1 L.arity => w ∈ carrier L.target) hValue)
    (L.special.toMap p₀).property

end PreparedKeyLabelSpecialPreparation
end IntegrationInACVF.Section7
