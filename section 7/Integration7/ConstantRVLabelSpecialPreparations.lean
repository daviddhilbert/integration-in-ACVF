import Integration7.UnarySpecialHeadPreparations

/-! A unary special preparation lifts to an arbitrary actual domain
whose full RV tuple is fixed and whose VF projection is the original
domain. This applies directly to the head image of an RV-class product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}

structure ConstantRVLabelSpecialPreparation
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (t : Fin l → RV (M := M)) (P : Base (M := M)) where
  source_mem : ∀ p ∈ carrier H, retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p ∈ carrier A
  source_surjective : ∀ a : A, ∃ p : H, retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val = a.val
  source_labels : ∀ p : H, p.val.2 = t
  arity : ℕ
  target : DefSet (M := M) S 1 arity
  projection : Fin b → Fin arity
  carried : Fin l → Fin arity
  special : SpecialBijection H target
  gamma : GammaChainDefinable P special.chain
  jointly_determine : RVLabelsJointlyDetermine (M := M) projection carried
  commutes : ∀ p : H, retainVFLabels projection (special.toMap p).val =
    (T.toMap ⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,source_mem _ p.property⟩).val
  labels : ∀ p : H, (special.toMap p).val.2 ∘ carried = t
  pullback : IsRVPullback (carrier target)

theorem gamma_constant_rv_label_special_preparation_exists
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B))
    (H : DefSet (M := M) S 1 l) (hH : GammaSetDefinable P (carrier H)) (t : Fin l → RV (M := M))
    (hHA : ∀ p ∈ carrier H, retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p ∈ carrier A)
    (hSurj : ∀ a : A, ∃ p : H, retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val = a.val)
    (hSource : ∀ p : H, p.val.2 = t) : Nonempty (ConstantRVLabelSpecialPreparation T H t P) := by
  have hJoint : RVLabelsJointlyDetermine (M := M) (Fin.elim0 : Fin 0 → Fin l) (id : Fin l → Fin l) :=
    fun _ _ _ h => h
  obtain ⟨r,K,σ,τ,W,hAlt,hW,hJoint',hCompare,hExtra⟩ := gamma_chain_lift_rv_labels T.chain hT
    H Fin.elim0 id hJoint hHA hH none T.alternating
  let V : SpecialBijection H K := ⟨W,hAlt⟩
  refine ⟨⟨hHA,hSurj,hSource,r,K,σ,τ,V,hW,hJoint',hCompare,
    fun p => (hExtra p).trans (hSource p),?_⟩⟩
  exact rv_label_lift_target_pullback T V Fin.elim0 id σ τ t hHA hSurj hSource
    hJoint' hCompare hExtra hB

namespace ConstantRVLabelSpecialPreparation
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {t : Fin l → RV (M := M)}

def head (L : ConstantRVLabelSpecialPreparation T H t P) : HeadPreparation H :=
  unarySpecialHeadPreparation L.special L.pullback

def program (L : ConstantRVLabelSpecialPreparation T H t P) :
    OrderedContractionProgram S H L.head.contractedSet := unarySpecialContractionProgram L.special L.pullback

theorem program_gamma (L : ConstantRVLabelSpecialPreparation T H t P) : GammaProgramDefinable P L.program :=
  gamma_unary_special_contraction_program L.special L.pullback L.gamma

theorem target_carrier (L : ConstantRVLabelSpecialPreparation T H t P) (q : Point (M := M) 1 L.arity) :
    q ∈ carrier L.target ↔ retainVFLabels L.projection q ∈ carrier B ∧ q.2 ∘ L.carried = t := by
  apply rv_label_lift_target_carrier T L.special Fin.elim0 id L.projection L.carried t
    L.source_mem L.source_surjective L.source_labels L.jointly_determine L.commutes
  intro p
  exact (L.labels p).trans (L.source_labels p).symm

def projectionMap (L : ConstantRVLabelSpecialPreparation T H t P) : Map L.target B :=
  mapIntoSubset (retainVFLabelsMap L.projection L.target) B
    (fun q => ((L.target_carrier q.val).mp q.property).1)

theorem projection_bijective (L : ConstantRVLabelSpecialPreparation T H t P) :
    Function.Bijective L.projectionMap := by
  constructor
  · intro p q he
    have hp := ((L.target_carrier p.val).mp p.property).2
    have hq := ((L.target_carrier q.val).mp q.property).2
    have hh : retainVFLabels L.projection p.val = retainVFLabels L.projection q.val := congrArg Subtype.val he
    have hVF0 := congrArg Prod.fst hh
    have hVF : p.val.1 = q.val.1 := hVF0
    have hRV0 := congrArg Prod.snd hh
    have hRV : p.val.2 ∘ L.projection = q.val.2 ∘ L.projection := hRV0
    exact Subtype.ext (Prod.ext hVF (L.jointly_determine p.val.2 q.val.2 hRV (hp.trans hq.symm)))
  · intro q
    obtain ⟨p,hp⟩ := L.source_surjective (T.inverseMap q)
    refine ⟨L.special.toMap p,Subtype.ext ?_⟩
    change retainVFLabels L.projection (L.special.toMap p).val = q.val
    rw [L.commutes]
    have he : (⟨retainVFLabels (Fin.elim0 : Fin 0 → Fin l) p.val,L.source_mem _ p.property⟩ : A) =
        T.inverseMap q := Subtype.ext hp
    rw [he,T.apply_inverse]

theorem projection_gamma (L : ConstantRVLabelSpecialPreparation T H t P) :
    GammaGraphDefinable P (pointMapGraph L.projectionMap) := by
  have h := gamma_retain_vf_labels_graph L.target L.projection
    (GammaChainDefinable.target P L.special.chain L.gamma)
  exact GammaGraphDefinable.congr h (fun _ _ => Iff.rfl)

theorem projection_contractible (L : ConstantRVLabelSpecialPreparation T H t P) : Contractible L.projectionMap :=
  fun _ _ h => same_rv_retain_vf_labels L.projection h

theorem inverse_projection_contractible (L : ConstantRVLabelSpecialPreparation T H t P) :
    Contractible (Map.inverse L.projectionMap L.projection_bijective) := by
  intro p q hpq
  let F := Map.inverse L.projectionMap L.projection_bijective
  have hp := ((L.target_carrier (F p).val).mp (F p).property).2
  have hq := ((L.target_carrier (F q).val).mp (F q).property).2
  have hP : retainVFLabels L.projection (F p).val = p.val :=
    congrArg Subtype.val (Map.apply_inverse L.projectionMap L.projection_bijective p)
  have hQ : retainVFLabels L.projection (F q).val = q.val :=
    congrArg Subtype.val (Map.apply_inverse L.projectionMap L.projection_bijective q)
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp hpq
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,L.jointly_determine (F p).val.2 (F q).val.2 ?_ (hp.trans hq.symm)⟩
  · intro i
    have hP' := congrArg (fun z : Point (M := M) 1 b => z.1 i) hP
    have hQ' := congrArg (fun z : Point (M := M) 1 b => z.1 i) hQ
    exact (congrArg rv hP').trans ((hVF i).trans (congrArg rv hQ').symm)
  · have hP' := congrArg Prod.snd hP
    have hQ' := congrArg Prod.snd hQ
    exact hP'.trans (hRV.trans hQ'.symm)

end ConstantRVLabelSpecialPreparation
end IntegrationInACVF.Section7
