import IntegrationSection5.RVProjectionNormalization

/-! The first-n presentation of a standard contraction, including the actual
natural lift bijection and the RV-category isomorphism to the original
explicit volume-selector presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.StandardContraction
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def normalizedObject (C : StandardContraction A σ) :=
  firstVolumeObject (Map.image (rawLabelMap C.target)) C.volumeIndex

def normalizationIso (C : StandardContraction A σ) : C.contractionObject ≅ C.normalizedObject :=
  firstVolumeIso (Map.image (rawLabelMap C.target)) C.volumeIndex

def normalizedContractionMap (C : StandardContraction A σ) :
    Map A (rvObjectDomain C.normalizedObject) :=
  Map.comp (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex) C.rawContractionMap

def normalizedNaturalRawMap (C : StandardContraction A σ) :
    Map A (PresentedSet.univ (rawPointSpace n (n+C.arity)) S) :=
  Map.comp (rawPointMap (PresentedSet.univ (pointSpace n (n+C.arity)) S))
    (Map.comp (canonicalMap (PresentedSet.univ (pointSpace n C.arity) S)) C.naturalMap)

theorem normalizedNaturalRawMap_labels (C : StandardContraction A σ) (a : A) :
    (C.normalizedNaturalRawMap a).val.2 = (C.normalizedContractionMap a).val := by
  funext j
  cases j using Fin.addCases with
  | left i =>
    change (canonical (C.naturalMap a).val).2 (Fin.castAdd C.arity i) =
      (C.toMap a).val.2 (prependVolumeIndex C.volumeIndex (Fin.castAdd C.arity i))
    rw [canonical_new,prependVolumeIndex,Fin.addCases_left]
    exact (C.naturalMap_rv a i).symm
  | right j =>
    change (canonical (C.naturalMap a).val).2 (Fin.natAdd n j) =
      (C.toMap a).val.2 (prependVolumeIndex C.volumeIndex (Fin.natAdd n j))
    rw [canonical_old,prependVolumeIndex,Fin.addCases_right]
    exact congrFun (C.naturalMap_labels a) j

theorem normalizedNaturalRawMap_mem_lift (C : StandardContraction A σ) (a : A) :
    (C.normalizedNaturalRawMap a).val ∈ carrier (rawLift C.normalizedObject) := by
  refine ⟨C.normalizedContractionMap a,(C.normalizedNaturalRawMap_labels a).symm,?_⟩
  funext i
  change (C.toMap a).val.2 (prependVolumeIndex C.volumeIndex (Fin.castAdd C.arity i)) =
    @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (CanonicalStructure.normalized_model hM) n (C.naturalMap a).val.1 i
  rw [normalized_tupleRV]
  rw [prependVolumeIndex,Fin.addCases_left]
  exact C.naturalMap_rv a i

def normalizedNaturalLiftMap (C : StandardContraction A σ) : Map A (rawLift C.normalizedObject) :=
  mapIntoSubset C.normalizedNaturalRawMap (rawLift C.normalizedObject) C.normalizedNaturalRawMap_mem_lift

theorem normalizedNaturalLiftMap_bijective (C : StandardContraction A σ) :
    Function.Bijective C.normalizedNaturalLiftMap := by
  constructor
  · intro a b hab
    apply C.naturalMap_injective
    have hv := congrArg (fun q : rawLift C.normalizedObject => q.val) hab
    exact Subtype.ext (canonical_injective hv)
  · intro q
    obtain ⟨u,hu,hvol⟩ := q.property
    obtain ⟨v,hv⟩ := u.property
    obtain ⟨w,hw⟩ := v.property
    have hqvol := hvol.trans (normalized_tupleRV (sM := sM) (hM := hM) (n := n) q.val.1)
    let p : Point (M := M) n C.arity := (q.val.1,w.val.2)
    have hLift : C.LiftCondition p := by
      refine ⟨w,rfl,?_⟩
      intro i
      have hv' := congrFun hv (Fin.castAdd C.arity i)
      have hw' := congrFun hw (C.volumeIndex i)
      have hq' := congrFun hqvol i
      change v.val (prependVolumeIndex C.volumeIndex (Fin.castAdd C.arity i)) =
        u.val (Fin.castAdd C.arity i) at hv'
      rw [prependVolumeIndex,Fin.addCases_left] at hv'
      exact hw'.trans (hv'.trans hq')
    obtain ⟨a,ha⟩ := C.naturalMap_surjective_lift p hLift
    refine ⟨a,Subtype.ext ?_⟩
    have hvf : (C.naturalMap a).val.1 = q.val.1 := congrArg (fun z : Point (M := M) n C.arity => z.1) ha
    refine Prod.ext hvf ?_
    funext j
    cases j using Fin.addCases with
    | left i =>
      change (canonical (C.naturalMap a).val).2 (Fin.castAdd C.arity i) = q.val.2 (Fin.castAdd C.arity i)
      rw [canonical_new]
      have hq' := congrFun hqvol i
      change u.val (Fin.castAdd C.arity i) = @rv M sM hM (q.val.1 i) at hq'
      exact (congrArg (@rv M sM hM) (congrFun hvf i)).trans (hq'.symm.trans (congrFun hu _))
    | right j =>
      change (canonical (C.naturalMap a).val).2 (Fin.natAdd n j) = q.val.2 (Fin.natAdd n j)
      rw [canonical_old]
      have hw' := congrFun hw j
      have hv' := congrFun hv (Fin.natAdd n j)
      change v.val (prependVolumeIndex C.volumeIndex (Fin.natAdd n j)) = u.val (Fin.natAdd n j) at hv'
      rw [prependVolumeIndex,Fin.addCases_right] at hv'
      exact (congrArg (fun z : Point (M := M) n C.arity => z.2 j) ha).trans
        (hw'.trans (hv'.trans (congrFun hu _)))

theorem normalizedNaturalLiftMap_square (C : StandardContraction A σ) (a : A) :
    (C.normalizedNaturalLiftMap a).val.2 = (C.normalizedContractionMap a).val :=
  C.normalizedNaturalRawMap_labels a

theorem normalizedObject_first (C : StandardContraction A σ)
    (u : rvObjectDomain C.normalizedObject) (i : Fin n) :
    (rvObjectVolume C.normalizedObject u).val i = u.val (Fin.castAdd C.arity i) := rfl

end IntegrationInACVF.Section5.StandardContraction
