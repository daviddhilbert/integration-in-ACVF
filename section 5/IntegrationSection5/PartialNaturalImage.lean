import IntegrationSection5.PartialNaturalMap

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
namespace IntegrationInACVF.Section5.PartialContractionProgram
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {p n m l : ℕ} {A : DefSet (M := M) S (p+n) m} {U : DefSet (M := M) S p l}

def LiftCondition (T : PartialContractionProgram S p (n := n) A U) (q : Point (M := M) (p+n) l) : Prop :=
  ∃ u : U, u.val.2 = q.2 ∧ (∀ j : Fin p, vfAt u.val j = vfAt q (frozenIndex p n j)) ∧
    ∀ i, u.val.2 (T.volumeIndex i) = rv (vfAt q (activeIndex p n i))

theorem naturalMap_liftCondition (T : PartialContractionProgram S p (n := n) A U) (a : A) :
    T.LiftCondition (T.naturalMap a).val :=
  ⟨T.toMap a,(T.naturalMap_labels a).symm,
    fun j => (T.toMap_frozen a j).trans (T.naturalMap_frozen a j).symm,T.naturalMap_rv a⟩

theorem naturalMap_surjective_lift (T : PartialContractionProgram S p (n := n) A U) :
    ∀ q : Point (M := M) (p+n) l, T.LiftCondition q → q ∈ carrier (Map.image T.naturalMap) := by
  induction T with
  | zero A =>
    rintro q ⟨u,hu,hf,_⟩
    exact ⟨u,Prod.ext (funext hf) hu⟩
  | @step n m l A U T tail ih =>
    rintro q ⟨u,hu,hf,hv⟩
    have hTail : tail.LiftCondition (dropHead id q) :=
      ⟨u,hu,hf,fun i => hv i.succ⟩
    obtain ⟨c,hc⟩ := ih (dropHead id q) hTail
    have hfinal : (tail.toMap c).val.2 = q.2 :=
      (tail.naturalMap_labels c).symm.trans (congrArg (fun p : Point (M := M) (p+n) l => p.2) hc)
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
      exact (T.lifting_square a).symm.trans ((congrArg (dropHead (n := p+n) (id : Fin (1+T.arity) → Fin (1+T.arity))) haVal).trans
        (dropHead_insertHead _ _))
    have hhead := congrArg (fun p : Point (M := M) ((p+n)+1) (1+T.arity) => vfAt p 0) haVal
    change vfAt (T.map a).val 0 = vfAt q 0 at hhead
    refine ⟨a,?_⟩
    refine (naturalMap_step T tail a).trans ?_
    rw [hca]
    exact (congrArg (insertHead (vfAt (T.map a).val 0)) hc).trans
      ((congrArg (fun x : VF (M := M) => insertHead x (dropHead id q)) hhead).trans (insertHead_dropHead q))

theorem naturalImage_exact (T : PartialContractionProgram S p (n := n) A U) (q : Point (M := M) (p+n) l) :
    q ∈ carrier (Map.image T.naturalMap) ↔ T.LiftCondition q := by
  constructor
  · rintro ⟨a,rfl⟩
    exact T.naturalMap_liftCondition a
  · exact T.naturalMap_surjective_lift q

def naturalImage (T : PartialContractionProgram S p (n := n) A U) : DefSet (M := M) S (p+n) l := Map.image T.naturalMap

def naturalBijection (T : PartialContractionProgram S p (n := n) A U) : Map A T.naturalImage := Map.toImage T.naturalMap

theorem naturalBijection_bijective (T : PartialContractionProgram S p (n := n) A U) :
    Function.Bijective T.naturalBijection := by
  constructor
  · intro a b h
    apply T.naturalMap_injective
    exact Subtype.ext (congrArg (fun p : T.naturalImage => p.val) h)
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

/-- The natural image contains every active RV polydisc with its frozen
VF tuple and all RV labels fixed. -/
theorem naturalImage_frozen_pullback (T : PartialContractionProgram S p (n := n) A U)
    (x y : Point (M := M) (p+n) l) (hx : x ∈ carrier T.naturalImage)
    (hxy : SameRV x y)
    (hfrozen : ∀ j : Fin p, vfAt x (frozenIndex p n j) = vfAt y (frozenIndex p n j)) :
    y ∈ carrier T.naturalImage := by
  obtain ⟨u,hu,hf,hv⟩ := (T.naturalImage_exact x).mp hx
  apply (T.naturalImage_exact y).mpr
  obtain ⟨hVF,hRV⟩ := (sameRV_iff _ _).mp hxy
  exact ⟨u,hu.trans hRV,fun j => (hf j).trans (hfrozen j),fun i => (hv i).trans (hVF _)⟩

end IntegrationInACVF.Section5.PartialContractionProgram
