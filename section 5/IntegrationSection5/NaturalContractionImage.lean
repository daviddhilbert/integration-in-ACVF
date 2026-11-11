import IntegrationSection5.NaturalContractionMap

/-! The natural map is a definable bijection onto exactly the lift specified
by the ordered contraction's RV image and its volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.OrderedContractionProgram
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}

def LiftCondition (T : OrderedContractionProgram S A U) (q : Point (M := M) n l) : Prop :=
  ∃ u : U, u.val.2 = q.2 ∧ ∀ i, u.val.2 (T.volumeIndex i) = rv (vfAt q i)

theorem naturalMap_liftCondition (T : OrderedContractionProgram S A U) (a : A) :
    T.LiftCondition (T.naturalMap a).val :=
  ⟨T.toMap a,(T.naturalMap_labels a).symm,T.naturalMap_rv a⟩

theorem naturalMap_surjective_lift (T : OrderedContractionProgram S A U) :
    ∀ q : Point (M := M) n l, T.LiftCondition q → q ∈ carrier (Map.image T.naturalMap) := by
  induction T with
  | zero A =>
    rintro q ⟨u,hu,_⟩
    exact ⟨u,Prod.ext (Subsingleton.elim _ _) hu⟩
  | @step n m l A U T tail ih =>
    rintro q ⟨u,hu,hv⟩
    have hTail : tail.LiftCondition (dropHead id q) :=
      ⟨u,hu,fun i => hv i.succ⟩
    obtain ⟨c,hc⟩ := ih (dropHead id q) hTail
    have hfinal : (tail.toMap c).val.2 = q.2 :=
      (tail.naturalMap_labels c).symm.trans (congrArg (fun p : Point (M := M) n l => p.2) hc)
    have hHead : c.val.2 (Fin.castAdd T.arity 0) = rv (vfAt q 0) := by
      calc
        _ = (tail.toMap c).val.2 (suffixIndex tail.rvArity_le 0) := (tail.oldLabels c 0).symm
        _ = q.2 (suffixIndex tail.rvArity_le 0) := congrFun hfinal _
        _ = u.val.2 (suffixIndex tail.rvArity_le 0) := (congrFun hu _).symm
        _ = rv (vfAt q 0) := hv 0
    let qLift := insertHead (vfAt q 0) c.val
    have hLift : qLift ∈ carrier T.liftSet := by
      apply (T.liftSet_exact qLift).mpr
      refine ⟨?_,hHead⟩
      simpa only [qLift,dropHead_insertHead] using c.property
    obtain ⟨a,ha⟩ := T.liftMap_bijective.2 ⟨qLift,hLift⟩
    have haVal := congrArg (fun p : T.liftSet => p.val) ha
    have hca : T.contractionMap a = c := by
      apply Subtype.ext
      exact (T.lifting_square a).symm.trans ((congrArg (dropHead (n := n) (id : Fin (1+T.arity) → Fin (1+T.arity))) haVal).trans
        (dropHead_insertHead _ _))
    have hhead := congrArg (fun p : Point (M := M) (n+1) (1+T.arity) => vfAt p 0) haVal
    change vfAt (T.map a).val 0 = vfAt q 0 at hhead
    refine ⟨a,?_⟩
    refine (naturalMap_step T tail a).trans ?_
    rw [hca]
    exact (congrArg (insertHead (vfAt (T.map a).val 0)) hc).trans
      ((congrArg (fun x : VF (M := M) => insertHead x (dropHead id q)) hhead).trans (insertHead_dropHead q))

theorem naturalImage_exact (T : OrderedContractionProgram S A U) (q : Point (M := M) n l) :
    q ∈ carrier (Map.image T.naturalMap) ↔ T.LiftCondition q := by
  constructor
  · rintro ⟨a,rfl⟩
    exact T.naturalMap_liftCondition a
  · exact T.naturalMap_surjective_lift q

def naturalImage (T : OrderedContractionProgram S A U) : DefSet (M := M) S n l := Map.image T.naturalMap

def naturalBijection (T : OrderedContractionProgram S A U) : Map A T.naturalImage := Map.toImage T.naturalMap

theorem naturalBijection_bijective (T : OrderedContractionProgram S A U) :
    Function.Bijective T.naturalBijection := by
  constructor
  · intro a b h
    apply T.naturalMap_injective
    exact Subtype.ext (congrArg (fun p : T.naturalImage => p.val) h)
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

theorem naturalImage_pullback (T : OrderedContractionProgram S A U) : IsRVPullback (carrier T.naturalImage) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q hpq
  obtain ⟨u,hu,hv⟩ := (T.naturalImage_exact p).mp hp
  apply (T.naturalImage_exact q).mpr
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp hpq
  exact ⟨u,hu.trans hRV,fun i => (hv i).trans (hVF i)⟩

end IntegrationInACVF.Section5.OrderedContractionProgram
