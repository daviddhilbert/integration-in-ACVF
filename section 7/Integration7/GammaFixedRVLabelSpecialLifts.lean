module

public import Integration7.GammaRVLabelChainLifts
public import Integration7.NativeFixedRVLabels
public import Integration7.RVLabelLiftTargetPullbacks

@[expose] public section

/-! Fixed RV tuples can be carried through actual special bijections.
The lifted target is an RV-pullback and its projection to the old target
is a genuine bijection with full graph over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {n a b d : ℕ}

def fixedRVLabelProjectionMap (A : DefSet (M := M) S n a) (t : Fin d → RV (M := M))
    (ht : ∀ i, (t i).val ∈ S) : Map (fixedRVLabelDomain A t ht) A :=
  mapIntoSubset (retainVFLabelsMap (Fin.castAdd d) (fixedRVLabelDomain A t ht)) A
    (fun p => ((fixed_rv_label_domain_carrier A t ht p.val).mp p.property).1)

structure FixedRVLabelSpecialLift
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : SpecialBijection A B) (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (P : Base (M := M)) where
  arity : ℕ
  target : DefSet (M := M) S n arity
  projection : Fin b → Fin arity
  carried : Fin d → Fin arity
  special : SpecialBijection (fixedRVLabelDomain A t ht) target
  gamma : GammaChainDefinable P special.chain
  jointly_determine : RVLabelsJointlyDetermine (M := M) projection carried
  commutes : ∀ p : fixedRVLabelDomain A t ht,
    retainVFLabels projection (special.toMap p).val = (T.toMap (fixedRVLabelProjectionMap A t ht p)).val
  labels : ∀ p : fixedRVLabelDomain A t ht, (special.toMap p).val.2 ∘ carried = t
  pullback : IsRVPullback (carrier target)

theorem gamma_fixed_rv_label_special_lift_exists
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain)
    (hB : IsRVPullback (carrier B)) (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (hTuple : DefinableOverBase P (fun _ : Fin d => .rv) {fun i => (t i).val}) :
    Nonempty (FixedRVLabelSpecialLift T t ht P) := by
  let H := fixedRVLabelDomain A t ht
  have hHA : ∀ p ∈ carrier H, retainVFLabels (Fin.castAdd d) p ∈ carrier A :=
    fun p hp => ((fixed_rv_label_domain_carrier A t ht p).mp hp).1
  have hSource : ∀ p : H, p.val.2 ∘ Fin.natAdd a = t :=
    fun p => ((fixed_rv_label_domain_carrier A t ht p.val).mp p.property).2
  have hH := gamma_fixed_rv_label_domain A (GammaChainDefinable.source P T.chain hT) t ht hTuple
  obtain ⟨r,K,σ,τ,W,hAlt,hW,hJoint,hCompare,hExtra⟩ := gamma_chain_lift_rv_labels T.chain hT
    H (Fin.castAdd d) (Fin.natAdd a) fixed_rv_labels_jointly_determine hHA hH none T.alternating
  let V : SpecialBijection H K := ⟨W,hAlt⟩
  refine ⟨⟨r,K,σ,τ,V,hW,hJoint,hCompare,fun p => (hExtra p).trans (hSource p),?_⟩⟩
  exact rv_label_lift_target_pullback T V (Fin.castAdd d) (Fin.natAdd a) σ τ t hHA
    (fixed_rv_label_projection_surjective A t ht) hSource hJoint hCompare hExtra hB

namespace FixedRVLabelSpecialLift
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
variable {T : SpecialBijection A B} {t : Fin d → RV (M := M)} {ht : ∀ i, (t i).val ∈ S}

theorem target_carrier (L : FixedRVLabelSpecialLift T t ht P) (q : Point (M := M) n L.arity) :
    q ∈ carrier L.target ↔ retainVFLabels L.projection q ∈ carrier B ∧ q.2 ∘ L.carried = t := by
  apply rv_label_lift_target_carrier T L.special (Fin.castAdd d) (Fin.natAdd a)
    L.projection L.carried t
    (fun p hp => ((fixed_rv_label_domain_carrier A t ht p).mp hp).1)
    (fixed_rv_label_projection_surjective A t ht)
    (fun p => ((fixed_rv_label_domain_carrier A t ht p.val).mp p.property).2)
    L.jointly_determine L.commutes
  intro p
  exact (L.labels p).trans (((fixed_rv_label_domain_carrier A t ht p.val).mp p.property).2.symm)

def projectionMap (L : FixedRVLabelSpecialLift T t ht P) : Map L.target B :=
  mapIntoSubset (retainVFLabelsMap L.projection L.target) B
    (fun q => ((L.target_carrier q.val).mp q.property).1)

theorem projection_bijective (L : FixedRVLabelSpecialLift T t ht P) :
    Function.Bijective L.projectionMap := by
  constructor
  · intro p q he
    have hp := ((L.target_carrier p.val).mp p.property).2
    have hq := ((L.target_carrier q.val).mp q.property).2
    have hh : retainVFLabels L.projection p.val = retainVFLabels L.projection q.val :=
      congrArg Subtype.val he
    have hVF0 := congrArg Prod.fst hh
    have hVF : p.val.1 = q.val.1 := hVF0
    have hRV0 := congrArg Prod.snd hh
    have hRV : p.val.2 ∘ L.projection = q.val.2 ∘ L.projection := hRV0
    apply Subtype.ext
    exact Prod.ext hVF (L.jointly_determine p.val.2 q.val.2 hRV (hp.trans hq.symm))
  · intro q
    obtain ⟨p,hp⟩ := fixed_rv_label_projection_surjective A t ht (T.inverseMap q)
    refine ⟨L.special.toMap p,Subtype.ext ?_⟩
    change retainVFLabels L.projection (L.special.toMap p).val = q.val
    rw [L.commutes]
    have he : fixedRVLabelProjectionMap A t ht p = T.inverseMap q := Subtype.ext hp
    rw [he,T.apply_inverse]

theorem projection_gamma (L : FixedRVLabelSpecialLift T t ht P) :
    GammaGraphDefinable P (pointMapGraph L.projectionMap) := by
  have h := gamma_retain_vf_labels_graph L.target L.projection
    (GammaChainDefinable.target P L.special.chain L.gamma)
  apply GammaGraphDefinable.congr h
  intro p q
  rfl

end FixedRVLabelSpecialLift
end IntegrationInACVF.Section7
