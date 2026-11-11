import IntegrationSection5.NaturalContractionImage
import Section5.PullbackLift

/-! The actual pinned RV object and natural definable bijection to its lift
for an ordered contraction program. The volume projection is explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

def rawLabelMap (U : DefSet (M := M) S 0 l) : Map U (PresentedSet.univ (rawRVSpace l) S) :=
  Map.comp (@SpecialTransformations.DefinableGeometry.Map.snd LRV M (@CanonicalStructure.normalize M sM)
    (rawVFSpace 0) (rawRVSpace l) S (PresentedSet.univ (rawPointSpace 0 l) S)) (rawPointMap U)

theorem rawLabelMap_apply (U : DefSet (M := M) S 0 l) (u : U) : (rawLabelMap U u).val = u.val.2 := rfl

namespace OrderedContractionProgram
variable {A : DefSet (M := M) S n m} {U : DefSet (M := M) S 0 l}

def contractionObject (T : OrderedContractionProgram S A U) :
    @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n :=
  @SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S n l
    (Map.image (rawLabelMap U)) (rawRVProjectionMap T.volumeIndex (Map.image (rawLabelMap U)))

def rawContractionMap (T : OrderedContractionProgram S A U) : Map A (rvObjectDomain T.contractionObject) :=
  Map.comp (Map.toImage (rawLabelMap U)) T.toMap

def naturalRawMap (T : OrderedContractionProgram S A U) :
    Map A (PresentedSet.univ (rawPointSpace n l) S) :=
  Map.comp (rawPointMap (PresentedSet.univ (pointSpace n l) S)) T.naturalMap

theorem naturalRawMap_mem_lift (T : OrderedContractionProgram S A U) (a : A) :
    (T.naturalRawMap a).val ∈ carrier (rawLift T.contractionObject) := by
  refine ⟨Map.toImage (rawLabelMap U) (T.toMap a),(T.naturalMap_labels a).symm,?_⟩
  funext i
  change (T.toMap a).val.2 (T.volumeIndex i) =
    @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (CanonicalStructure.normalized_model hM) n (T.naturalMap a).val.1 i
  rw [normalized_tupleRV]
  exact T.naturalMap_rv a i

def naturalLiftMap (T : OrderedContractionProgram S A U) : Map A (rawLift T.contractionObject) :=
  mapIntoSubset T.naturalRawMap (rawLift T.contractionObject) T.naturalRawMap_mem_lift

theorem naturalLiftMap_apply (T : OrderedContractionProgram S A U) (a : A) :
    (T.naturalLiftMap a).val = (T.naturalMap a).val := rfl

theorem naturalLiftMap_bijective (T : OrderedContractionProgram S A U) :
    Function.Bijective T.naturalLiftMap := by
  constructor
  · intro a b hab
    apply T.naturalMap_injective
    have hv := congrArg (fun q : rawLift T.contractionObject => q.val) hab
    exact Subtype.ext hv
  · intro q
    obtain ⟨u,hu,hvol⟩ := q.property
    obtain ⟨v,hv⟩ := u.property
    have hv' : v.val.2 = u.val := (rawLabelMap_apply U v).symm.trans hv
    let p : Point (M := M) n l := q.val
    have hLift : T.LiftCondition p := by
      refine ⟨v,hv'.trans hu,?_⟩
      intro i
      have h := congrFun hvol i
      change u.val (T.volumeIndex i) =
        @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
          (CanonicalStructure.normalized_model hM) n p.1 i at h
      rw [normalized_tupleRV] at h
      exact (congrFun hv' _).trans h
    obtain ⟨a,ha⟩ := T.naturalMap_surjective_lift p hLift
    exact ⟨a,Subtype.ext ha⟩

theorem naturalLiftMap_square (T : OrderedContractionProgram S A U) (a : A) :
    (T.naturalLiftMap a).val.2 = (T.rawContractionMap a).val := T.naturalMap_labels a

theorem rawContractionMap_surjective (T : OrderedContractionProgram S A U) :
    Function.Surjective T.rawContractionMap := by
  rintro ⟨q,u,hu⟩
  obtain ⟨a,ha⟩ := T.surjective u
  refine ⟨a,Subtype.ext ?_⟩
  change (rawLabelMap U (T.toMap a)).val = q
  rw [ha]
  exact hu

end OrderedContractionProgram
end IntegrationInACVF.Section5
