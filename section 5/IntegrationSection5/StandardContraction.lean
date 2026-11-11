import IntegrationSection5.GammaOrderedContraction
import IntegrationSection5.StandardContractionLift
import IntegrationSection5.VFPermutation

/-! Definition5.5: an actual sequence of relative preparations in a specified
VF-coordinate order. The natural map restores the original VF ordering and
retains the explicit volume projection on the resulting RV domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

structure StandardContraction (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) where
  arity : ℕ
  target : DefSet (M := M) S 0 arity
  program : OrderedContractionProgram S (vfPermutationImage A σ) target

namespace StandardContraction
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def toMap (C : StandardContraction A σ) : Map A C.target :=
  Map.comp C.program.toMap (vfPermutationBijection A σ)

def volumeIndex (C : StandardContraction A σ) (i : Fin n) : Fin C.arity := C.program.volumeIndex (σ.symm i)

theorem volumeIndex_injective (C : StandardContraction A σ) : Function.Injective C.volumeIndex :=
  C.program.volumeIndex_injective.comp σ.symm.injective

def naturalMap (C : StandardContraction A σ) : Map A (PresentedSet.univ (pointSpace n C.arity) S) :=
  Map.comp (vfPermutationMap (PresentedSet.univ (pointSpace n C.arity) S) σ.symm)
    (Map.comp C.program.naturalMap (vfPermutationBijection A σ))

theorem naturalMap_labels (C : StandardContraction A σ) (a : A) :
    (C.naturalMap a).val.2 = (C.toMap a).val.2 := C.program.naturalMap_labels (vfPermutationBijection A σ a)

theorem naturalMap_rv (C : StandardContraction A σ) (a : A) (i : Fin n) :
    (C.toMap a).val.2 (C.volumeIndex i) = rv (vfAt (C.naturalMap a).val i) :=
  C.program.naturalMap_rv (vfPermutationBijection A σ a) (σ.symm i)

theorem naturalMap_injective (C : StandardContraction A σ) : Function.Injective C.naturalMap := by
  intro a b hab
  have hval := congrArg (fun p : PresentedSet.univ (pointSpace n C.arity) S => p.val) hab
  have hP := vfPermutation_injective σ.symm hval
  have hQ := C.program.naturalMap_injective (Subtype.ext hP)
  exact (vfPermutationBijection_bijective A σ).1 hQ

def LiftCondition (C : StandardContraction A σ) (q : Point (M := M) n C.arity) : Prop :=
  ∃ u : C.target, u.val.2 = q.2 ∧ ∀ i, u.val.2 (C.volumeIndex i) = rv (vfAt q i)

theorem naturalMap_surjective_lift (C : StandardContraction A σ) (q : Point (M := M) n C.arity)
    (hq : C.LiftCondition q) : q ∈ carrier (Map.image C.naturalMap) := by
  obtain ⟨u,hu,hv⟩ := hq
  have hLift : C.program.LiftCondition (vfPermutation σ q) := by
    refine ⟨u,hu,?_⟩
    intro j
    have h := hv (σ j)
    change u.val.2 (C.program.volumeIndex (σ.symm (σ j))) = rv (vfAt q (σ j)) at h
    rw [σ.symm_apply_apply j] at h
    exact h
  obtain ⟨b,hb⟩ := C.program.naturalMap_surjective_lift (vfPermutation σ q) hLift
  obtain ⟨a,ha⟩ := (vfPermutationBijection_bijective A σ).2 b
  refine ⟨a,?_⟩
  change vfPermutation σ.symm (C.program.naturalMap (vfPermutationBijection A σ a)).val = q
  rw [ha]
  exact (congrArg (vfPermutation σ.symm) hb).trans (vfPermutation_inverse σ q)

def contractionObject (C : StandardContraction A σ) :
    @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S n :=
  @SpecialTransformations.Section4.RVObject.mk M (@CanonicalStructure.normalize M sM) S n C.arity
    (Map.image (rawLabelMap C.target))
    (rawRVProjectionMap C.volumeIndex (Map.image (rawLabelMap C.target)))

def rawContractionMap (C : StandardContraction A σ) : Map A (rvObjectDomain C.contractionObject) :=
  Map.comp (Map.toImage (rawLabelMap C.target)) C.toMap

def naturalRawMap (C : StandardContraction A σ) : Map A (PresentedSet.univ (rawPointSpace n C.arity) S) :=
  Map.comp (rawPointMap (PresentedSet.univ (pointSpace n C.arity) S)) C.naturalMap

theorem naturalRawMap_mem_lift (C : StandardContraction A σ) (a : A) :
    (C.naturalRawMap a).val ∈ carrier (rawLift C.contractionObject) := by
  refine ⟨Map.toImage (rawLabelMap C.target) (C.toMap a),(C.naturalMap_labels a).symm,?_⟩
  funext i
  change (C.toMap a).val.2 (C.volumeIndex i) =
    @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (CanonicalStructure.normalized_model hM) n (C.naturalMap a).val.1 i
  rw [normalized_tupleRV]
  exact C.naturalMap_rv a i

def naturalLiftMap (C : StandardContraction A σ) : Map A (rawLift C.contractionObject) :=
  mapIntoSubset C.naturalRawMap (rawLift C.contractionObject) C.naturalRawMap_mem_lift

theorem naturalLiftMap_bijective (C : StandardContraction A σ) : Function.Bijective C.naturalLiftMap := by
  constructor
  · intro a b hab
    apply C.naturalMap_injective
    have hv := congrArg (fun q : rawLift C.contractionObject => q.val) hab
    exact Subtype.ext hv
  · intro q
    obtain ⟨u,hu,hvol⟩ := q.property
    obtain ⟨v,hv⟩ := u.property
    have hv' : v.val.2 = u.val := (rawLabelMap_apply C.target v).symm.trans hv
    let p : Point (M := M) n C.arity := q.val
    have hLift : C.LiftCondition p := by
      refine ⟨v,hv'.trans hu,?_⟩
      intro i
      have h := congrFun hvol i
      change u.val (C.volumeIndex i) =
        @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
          (CanonicalStructure.normalized_model hM) n p.1 i at h
      rw [normalized_tupleRV] at h
      exact (congrFun hv' _).trans h
    obtain ⟨a,ha⟩ := C.naturalMap_surjective_lift p hLift
    exact ⟨a,Subtype.ext ha⟩

theorem naturalLiftMap_square (C : StandardContraction A σ) (a : A) :
    (C.naturalLiftMap a).val.2 = (C.rawContractionMap a).val := C.naturalMap_labels a

end StandardContraction

/-- Every permutation has an actual contraction sequence and original-Gamma
contracted set and complete contraction graph. No sequence is a premise. -/
theorem standard_contraction_exists {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (P : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk P.real < κ) (F : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable P (carrier A)) (σ : Equiv.Perm (Fin n)) :
    ∃ C : StandardContraction A σ, GammaSetDefinable P (carrier C.target) ∧
      GammaGraphDefinable P (pointMapGraph C.toMap) := by
  obtain ⟨l,U,T,hU,hT⟩ := gamma_ordered_contraction_program hs h00 P hsmall F hPS n
    (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ)
  refine ⟨⟨l,U,T⟩,hU,?_⟩
  exact gamma_composition_graph (vfPermutationBijection A σ) T.toMap (gamma_vfPermutation_graph A hA σ) hT

end IntegrationInACVF.Section5
