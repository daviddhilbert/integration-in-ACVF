module

public import Integration7.HKDensityLabelConstraints

@[expose] public section

/-! Prepared RV descent changes only the base coordinates. Exact equality
of retained density labels therefore survives even away from chosen rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b : ℕ}

theorem prepared_relation_density_eq
    {A : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}
    (T : SpecialBijection A Z) (hT : GammaChainDefinable B T.chain)
    (H : GammaRelationFormula B p a b (fun _ => .vf)) (δ : Fin a) (ε : Fin b)
    (hH : H.val ⊆ densityLabelConstraint (fun _ => .vf) δ ε)
    (t : Fin (p+l) → RV (M := M)) (r : Fin a → RV (M := M)) (s : Fin b → RV (M := M))
    (h : Fin.append (Fin.append (rvValues t) (rvValues r)) (rvValues s) ∈
      ((GammaParameterRecode.prepared T hT).relation H).val) : r δ = s ε := by
  have hf := ((H.flatten.preparedDescend T hT).unflattenRV_append t r s).mp h
  have hr := (gammaRawRVGraph_append_iff _ (Fin.elim0,t) (Fin.elim0,Fin.append r s)).mp hf
  obtain ⟨q,_,hrow⟩ := hr
  have hraw := (H.vfRelation_append (T.inverseMap q).val r s).mp hrow
  exact (density_label_constraint_append δ ε (vfValues (T.inverseMap q).val.1)
    (fun j => ((T.inverseMap q).val.1 j).property) r s).mp (hH hraw)

theorem rv_relation_density_constraint
    (H : GammaRelationFormula B p a b (fun _ => .rv)) (δ : Fin a) (ε : Fin b)
    (hH : ∀ (t : Fin p → RV (M := M)) (r : Fin a → RV (M := M)) (s : Fin b → RV (M := M)),
      Fin.append (Fin.append (rvValues t) (rvValues r)) (rvValues s) ∈ H.val → r δ = s ε) :
    H.val ⊆ densityLabelConstraint (fun _ => .rv) δ ε := by
  intro w hw
  have hs := H.property.proper w hw
  let t : Fin p → RV (M := M) := fun j => ⟨w (Fin.castAdd b (Fin.castAdd a j)),by
    simpa only [Fin.append_left,sortEval,iRV] using hs (Fin.castAdd b (Fin.castAdd a j))⟩
  let r : Fin a → RV (M := M) := fun j => ⟨w (Fin.castAdd b (Fin.natAdd p j)),by
    simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hs (Fin.castAdd b (Fin.natAdd p j))⟩
  let s : Fin b → RV (M := M) := fun j => ⟨w (Fin.natAdd (p+a) j),by
    simpa only [Fin.append_right,sortEval,iRV] using hs (Fin.natAdd (p+a) j)⟩
  have hp : Fin.append (Fin.append (rvValues t) (rvValues r)) (rvValues s) = w := by
    change Fin.append (Fin.append (fun j => w (Fin.castAdd b (Fin.castAdd a j)))
      (fun j => w (Fin.castAdd b (Fin.natAdd p j)))) (fun j => w (Fin.natAdd (p+a) j)) = w
    have hl := Fin.append_castAdd_natAdd (f := fun j : Fin (p+a) => w (Fin.castAdd b j))
    exact (congrArg (fun v => Fin.append v (fun j => w (Fin.natAdd (p+a) j))) hl).trans
      (Fin.append_castAdd_natAdd (f := w))
  exact ⟨congrArg Subtype.val (hH t r s (hp.symm ▸ hw)),hs⟩

theorem prepared_relation_density_constraint
    {A : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p l}
    (T : SpecialBijection A Z) (hT : GammaChainDefinable B T.chain)
    (H : GammaRelationFormula B p a b (fun _ => .vf)) (δ : Fin a) (ε : Fin b)
    (hH : H.val ⊆ densityLabelConstraint (fun _ => .vf) δ ε) :
    ((GammaParameterRecode.prepared T hT).relation H).val ⊆
      densityLabelConstraint (fun _ => .rv) δ ε :=
  rv_relation_density_constraint _ δ ε (prepared_relation_density_eq T hT H δ ε hH)

end IntegrationInACVF.Section7.HK
