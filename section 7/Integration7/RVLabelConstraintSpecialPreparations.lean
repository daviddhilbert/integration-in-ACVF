module

public import Integration7.RVLabelConstraintLiftTargets
public import Integration7.GammaRVLabelChainLifts
public import Integration7.UnarySpecialHeadPreparations

@[expose] public section

/-! A special preparation of a labelled unary domain lifts over an
arbitrary RV constraint, retaining all shared and carried labels. This
includes the second stage of a shared-label rectangle contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l : ℕ}

structure RVLabelConstraintSpecialPreparation
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (Q : DefSet (M := M) S 0 l) (ρ : Fin a → Fin l) (P : Base (M := M)) where
  source_shape : ∀ p : Point (M := M) 1 l, p ∈ carrier H ↔
    retainVFLabels ρ p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q
  arity : ℕ
  target : DefSet (M := M) S 1 arity
  projection : Fin b → Fin arity
  carried : Fin l → Fin arity
  special : SpecialBijection H target
  gamma : GammaChainDefinable P special.chain
  jointly_determine : RVLabelsJointlyDetermine (M := M) projection carried
  commutes : ∀ p : H, retainVFLabels projection (special.toMap p).val =
    (T.toMap ⟨retainVFLabels ρ p.val,((source_shape p.val).mp p.property).1⟩).val
  parameters : ∀ p : H, (special.toMap p).val.2 ∘ carried = p.val.2
  pullback : IsRVPullback (carrier target)

theorem gamma_rv_label_constraint_special_preparation_exists
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B))
    (H : DefSet (M := M) S 1 l) (hH : GammaSetDefinable P (carrier H))
    (Q : DefSet (M := M) S 0 l) (ρ : Fin a → Fin l)
    (hSource : ∀ p : Point (M := M) 1 l, p ∈ carrier H ↔
      retainVFLabels ρ p ∈ carrier A ∧ (Fin.elim0,p.2) ∈ carrier Q) :
    Nonempty (RVLabelConstraintSpecialPreparation T H Q ρ P) := by
  have hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A :=
    fun p hp => ((hSource p).mp hp).1
  have hJoint : RVLabelsJointlyDetermine (M := M) ρ (id : Fin l → Fin l) := fun _ _ _ h => h
  obtain ⟨r,K,σ,τ,W,hAlt,hW,hJoint',hCompare,hExtra⟩ := gamma_chain_lift_rv_labels T.chain hT
    H ρ id hJoint hHA hH none T.alternating
  let V : SpecialBijection H K := ⟨W,hAlt⟩
  exact ⟨⟨hSource,r,K,σ,τ,V,hW,hJoint',hCompare,hExtra,
    rv_label_constraint_lift_target_pullback T V Q ρ σ τ hSource hJoint' hCompare hExtra hB⟩⟩

namespace RVLabelConstraintSpecialPreparation
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l}
variable {Q : DefSet (M := M) S 0 l} {ρ : Fin a → Fin l}

def head (L : RVLabelConstraintSpecialPreparation T H Q ρ P) : HeadPreparation H :=
  unarySpecialHeadPreparation L.special L.pullback

def program (L : RVLabelConstraintSpecialPreparation T H Q ρ P) :
    OrderedContractionProgram S H L.head.contractedSet := unarySpecialContractionProgram L.special L.pullback

theorem program_gamma (L : RVLabelConstraintSpecialPreparation T H Q ρ P) :
    GammaProgramDefinable P L.program :=
  gamma_unary_special_contraction_program L.special L.pullback L.gamma

theorem target_carrier (L : RVLabelConstraintSpecialPreparation T H Q ρ P) (q : Point (M := M) 1 L.arity) :
    q ∈ carrier L.target ↔ retainVFLabels L.projection q ∈ carrier B ∧
      (Fin.elim0,q.2 ∘ L.carried) ∈ carrier Q ∧
      (q.2 ∘ L.projection) ∘ suffixIndex (special_chain_rvArity_le T.chain) = (q.2 ∘ L.carried) ∘ ρ :=
  rv_label_constraint_lift_target_carrier T L.special Q ρ L.projection L.carried L.source_shape
    L.jointly_determine L.commutes L.parameters q

end RVLabelConstraintSpecialPreparation
end IntegrationInACVF.Section7
