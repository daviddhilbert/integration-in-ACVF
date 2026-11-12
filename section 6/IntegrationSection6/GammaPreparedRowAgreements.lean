import IntegrationSection6.GammaPreparedFormulaDescent
import IntegrationSection6.GammaPrimitiveVFCodes

/-! Constancy on prepared polydiscs gives exact primitive-row agreement
between a VF representative and the descended RV-key formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b k : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}

def rawVFParameter (z : Point (M := M) p 0) : Fin p → M := fun j => (z.1 j).val

def rawPreparedKey (x : Point (M := M) p l) : Fin (p+l) → M := fun j => ((flatKey x).2 j).val

theorem GammaRelationFormula.vfRelation_split
    (R : GammaRelationFormula B p a b (fun _ => .vf))
    (z : Point (M := M) p 0) (v : Point (M := M) 0 (a+b)) :
    R.vfRelation z v ↔ Fin.append (Fin.append (rawVFParameter z)
      (fun j => (v.2 (Fin.castAdd b j)).val)) (fun j => (v.2 (Fin.natAdd a j)).val) ∈ R.val := by
  have h := R.vfRelation_append z (v.2 ∘ Fin.castAdd b) (v.2 ∘ Fin.natAdd a)
  simp only [Function.comp_def] at h
  rw [Fin.append_castAdd_natAdd (f := v.2)] at h
  have he : (Fin.elim0,v.2) = v := Prod.ext (Subsingleton.elim _ _) rfl
  rw [he] at h
  exact h

theorem gamma_prepared_domain_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (D : GammaDomainFormula B p a (fun _ => .vf))
    (hD : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).DomainAgreement D
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).DomainAgreement D
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  apply gammaDomainRows_agree_of_typed D (D.preparedDescend T hT)
  intro u
  exact (D.preparedDescend_row T hT (fun x y hxy v => hD x y hxy (fun j => (v.2 j).val)) x u).symm

theorem gamma_prepared_relation_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (R : GammaRelationFormula B p a b (fun _ => .vf))
    (hR : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).RelationAgreement R
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).RelationAgreement R
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  have hr : ∀ x y : C, SameRV x.val y.val → ∀ v,
      R.vfRelation (T.inverseMap x).val v ↔ R.vfRelation (T.inverseMap y).val v := by
    intro x y hxy v
    rw [R.vfRelation_split,R.vfRelation_split]
    exact hR x y hxy _ _
  apply gammaRelationRows_agree_of_typed R (R.flatten.preparedDescend T hT).unflattenRV
  intro u v
  exact (R.vfRelation_append (T.inverseMap x).val u v).symm.trans
    ((R.flatten.preparedDescend_row T hT hr x (Fin.append u v)).symm.trans
      ((R.flatten.preparedDescend T hT).unflattenRV_append (flatKey x.val).2 u v).symm)

theorem gamma_prepared_object_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (F : GammaFiniteRVSchema B p a k (fun _ => .vf))
    (hF : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).ObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).ObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_domain_agreement T hT ⟨F.domain,F.domain_definable⟩
      (fun x y hxy => (hF x y hxy).1) x,
    gamma_prepared_relation_agreement T hT ⟨F.volume,F.volume_definable⟩
      (fun x y hxy => (hF x y hxy).2) x⟩

theorem gamma_prepared_iso_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (F : GammaFiniteRVIsoSchema B p a b k (fun _ => .vf))
    (hF : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).IsoAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).IsoAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_object_agreement T hT F.source (fun x y hxy => (hF x y hxy).1) x,
    gamma_prepared_object_agreement T hT F.target (fun x y hxy => (hF x y hxy).2.1) x,
    gamma_prepared_relation_agreement T hT ⟨F.chart,F.chart_definable⟩
      (fun x y hxy => (hF x y hxy).2.2) x⟩

end IntegrationInACVF.Section6
