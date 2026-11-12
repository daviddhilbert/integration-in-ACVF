import IntegrationSection6.FocusRootDomains
import Section5.PullbackLift
import Section4.FunctionalRelations

/-! A full-graph definable selector from a root set valid on whole RV fibres.
This uses uniqueness, not definable choice for arbitrary finite fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def rootSelectorRelation (A : DefSet (M := M) S n m) (R : Set (Fin n → M)) (j : Fin n)
    (p : Point (M := M) n m) (b : Fin n → VF (M := M)) : Prop :=
  p ∈ carrier A ∧ (fun i => (b i).val) ∈ R ∧
    (∀ i, rv (b i) = rv (p.1 i)) ∧ ∀ i, i ≠ j → b i = p.1 i

theorem rootSelectorRelation_definable (A : DefSet (M := M) S n m)
    (R : Set (Fin n → M)) (hR : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n) R) (j : Fin n) :
    RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace n) S
      (rootSelectorRelation A R j) := by
  let ι := (Fin n ⊕ Fin m) ⊕ Fin n
  have hA := @Set.Definable.preimage_comp M S LRV (@CanonicalStructure.normalize M sM) _ _ (Sum.inl : Fin n ⊕ Fin m → ι) _ (setDefinable A)
  have hB := @SpecialTransformations.DefinableGeometry.Space.domain_definable LRV M (@CanonicalStructure.normalize M sM)
    (@SpecialTransformations.Section4.vfSpace M sM hM n)
  have hBd := @Set.Definable.preimage_comp M S LRV (@CanonicalStructure.normalize M sM) _ _ (Sum.inr : Fin n → ι) _
    (@Set.Definable.mono M ∅ LRV (@CanonicalStructure.normalize M sM) _ S _ hB (Set.empty_subset S))
  have hRd := @Set.Definable.preimage_comp M S LRV (@CanonicalStructure.normalize M sM) _ _ (Sum.inr : Fin n → ι) _ hR
  have hrv (i : Fin n) : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) ι
      {z | rvCode (z (.inr i)) = rvCode (z (.inl (.inl i)))} := by
    have hf := rvCode_definable S (.inr i : ι)
    have hg := rvCode_definable S (.inl (.inl i) : ι)
    letI := (@CanonicalStructure.normalize M sM)
    exact hf.ofPred_eq hg
  have heq (i : {i : Fin n // i ≠ j}) : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) ι
      {z | z (.inr i.val) = z (.inl (.inl i.val))} := by
    have hf := rawProj S (.inr i.val : ι)
    have hg := rawProj S (.inl (.inl i.val) : ι)
    letI := (@CanonicalStructure.normalize M sM)
    exact hf.ofPred_eq hg
  have hraw := by
    letI := (@CanonicalStructure.normalize M sM)
    exact (hA.inter hBd).inter
      (hRd.inter ((Set.definable_iInter_of_finite hrv).inter
        (Set.definable_iInter_of_finite heq)))
  change @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) ι _
  convert hraw using 1
  ext z
  constructor
  · rintro ⟨hp,hb,hpA,hbR,hrv,hother⟩
    refine ⟨⟨⟨hp,hpA⟩,hb⟩,hbR,?_,?_⟩
    · apply Set.mem_iInter.mpr
      intro i
      have he := congrArg Subtype.val (hrv i)
      change iRv (z (.inr i)) = iRv (z (.inl (.inl i))) at he
      change rvCode (z (.inr i)) = rvCode (z (.inl (.inl i)))
      exact (rvCode_eq (z (.inr i)) (hb i)).trans
        (he.trans (rvCode_eq (z (.inl (.inl i))) (hp.1 i)).symm)
    · apply Set.mem_iInter.mpr
      intro i
      exact congrArg Subtype.val (hother i.val i.property)
  · rintro ⟨⟨⟨hp,hpA⟩,hb⟩,hbR,hrv,hother⟩
    refine ⟨hp,hb,hpA,hbR,?_,?_⟩
    · intro i
      apply Subtype.ext
      have he := Set.mem_iInter.mp hrv i
      change rvCode (z (.inr i)) = rvCode (z (.inl (.inl i))) at he
      exact (rvCode_eq (z (.inr i)) (hb i)).symm.trans
        (he.trans (rvCode_eq (z (.inl (.inl i))) (hp.1 i)))
    · intro i hi
      exact Subtype.ext (Set.mem_iInter.mp hother ⟨i,hi⟩)

variable (A : DefSet (M := M) S n m) (R : Set (Fin n → M)) (j : Fin n)
variable (hcover : ∀ p ∈ carrier A,
  (fun i => (rv (p.1 i)).val) ∈ @rootDomain M (@CanonicalStructure.normalize M sM) n R j)

include hcover

theorem rootSelector_exists (a : A) : ∃ b, rootSelectorRelation A R j a.val b := by
  have ha : (fun i => (a.val.1 i).val) ∈
      @SpecialTransformations.Section7.rawTupleFibre M (@CanonicalStructure.normalize M sM) n (fun i => (rv (a.val.1 i)).val) := by
    intro i
    exact ⟨(a.val.1 i).property, rvCode_eq _ (a.val.1 i).property⟩
  obtain ⟨b,hb,_⟩ := hcover a.val a.property _ ha
  let bVF : Fin n → VF (M := M) := fun i => ⟨b i, (hb.1 i).1⟩
  refine ⟨bVF, a.property, hb.2.1, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact (rvCode_eq _ (bVF i).property).symm.trans (hb.1 i).2
  · intro i hi
    exact Subtype.ext (hb.2.2 i hi)

theorem rootSelector_unique (p : Point (M := M) n m)
    (b c : Fin n → VF (M := M))
    (hb : rootSelectorRelation A R j p b) (hc : rootSelectorRelation A R j p c) : b = c := by
  have ha : (fun i => (p.1 i).val) ∈
      @SpecialTransformations.Section7.rawTupleFibre M (@CanonicalStructure.normalize M sM) n (fun i => (rv (p.1 i)).val) := by
    intro i; exact ⟨(p.1 i).property, rvCode_eq _ (p.1 i).property⟩
  have h := hcover p hb.1 _ ha
  have hmem (d : Fin n → VF (M := M)) (hd : rootSelectorRelation A R j p d) :
      (fun i => (d i).val) ∈ @SpecialTransformations.Section7.rawTupleFibre M (@CanonicalStructure.normalize M sM) n
          (fun i => (rv (p.1 i)).val) ∧ (fun i => (d i).val) ∈ R ∧
        ∀ i, i ≠ j → (d i).val = (p.1 i).val := by
    refine ⟨?_,hd.2.1,fun i hi => congrArg Subtype.val (hd.2.2.2 i hi)⟩
    intro i
    exact ⟨(d i).property,(rvCode_eq _ (d i).property).trans
      (congrArg Subtype.val (hd.2.2.1 i))⟩
  have he := h.unique (hmem b hb) (hmem c hc)
  funext i
  exact Subtype.ext (congrFun he i)

def rootSelectionMap (hR : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n) R) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace n) S) :=
  @SpecialTransformations.DefinableGeometry.Map.ofFunctionalRelation LRV M (@CanonicalStructure.normalize M sM) _ _ _ _ _ _
    (rootSelectorRelation_definable A R hR j)
    (fun _ _ h => ⟨h.1,Set.mem_univ _⟩)
    (rootSelector_exists A R j hcover) (rootSelector_unique A R j hcover)

theorem rootSelectionMap_spec (hR : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n) R) (a : A) :
    rootSelectorRelation A R j a.val (rootSelectionMap A R j hcover hR a).val :=
  @SpecialTransformations.DefinableGeometry.Map.ofFunctionalRelation_graph LRV M (@CanonicalStructure.normalize M sM) _ _ _ _ _ _ _ _ _ _ a

end IntegrationInACVF.Section6
