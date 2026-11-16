module

public import Integration7.NativeVolumeDomains
public import IntegrationSection6.ActualRVFibreDefinability
public import Section4.FullDimension
public import Section9.MixedGenericDifferentiation

@[expose] public section

/-! Every realized RV polydisc with nonzero VF tags contains a VF tuple
independent over any specified small original real base. RV names do not
enlarge its VF parameter field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rawTupleRVPolydisc {n : ℕ} (S : Set M) (t : Fin n → CanonicalRV.RVSort M) :
    DefSet (rawVFSpace (M := M) n) (S ∪ Set.range (rvValues t)) where
  carrier := {x | tupleRV x = t}
  definable := by
    have he : (rawVFSpace (M := M) n).preimage {x | tupleRV x = t} =
        tupleRVFibre (rvValues t) := by
      ext z
      constructor
      · rintro ⟨hz,hx⟩ i
        let x := (rawVFSpace (M := M) n).decode ⟨z,hz⟩
        have hv := congrFun (vfValues_decode ⟨z,hz⟩) i
        change (x i).val = z i at hv
        refine ⟨hv ▸ (x i).property,?_⟩
        exact (congrArg iRv hv).symm.trans (congrArg Subtype.val (congrFun hx i))
      · intro hz
        let x : Fin n → VFType (M := M) := fun i => ⟨z i,(hz i).1⟩
        have hdom : z ∈ (rawVFSpace (M := M) n).domain := ⟨x,rfl⟩
        refine ⟨hdom,?_⟩
        have hx : (rawVFSpace (M := M) n).decode ⟨z,hdom⟩ = x :=
          vfValues_injective (vfValues_decode _)
        rw [hx]
        funext i
        exact Subtype.ext (hz i).2
    change (S ∪ Set.range (rvValues t)).Definable LRV _
    rw [he]
    exact (IntegrationInACVF.Section6.actualRVFibre_definable S t).raw_definable

set_option maxHeartbeats 1600000 in
theorem exists_independent_in_nonzero_rv_polydisc {κ : Cardinal} {n : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (t : Fin n → CanonicalRV.RVSort M) (ht : ∀ i, (t i).val ≠ iRVZero) :
    ∃ x : Fin n → VFType (M := M), tupleRV x = t ∧ AlgebraicIndependent (vfParameterField S) x := by
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  let R := S ∪ Set.range (rvValues t)
  have hR : Cardinal.mk R < κ := small_union_range hκ S hsmall (rvValues t)
  let A := (rawTupleRVPolydisc S t).prod (DefSet.univ (rawRVSpace (M := M) 0) R)
  obtain ⟨c,hcRV⟩ := tupleRV_surjective t
  have hc0 (i : Fin n) : c i ≠ 0 := by
    intro hz
    exact ht i ((congrArg Subtype.val (congrFun hcRV i)).symm.trans
      ((CanonicalRV.encodedRv_zero_iff _).mpr hz))
  let D : ValuedPolydisc (Valued.v : Valuation (VFType (M := M)) (Values.presentationType (M := M))) n :=
    ⟨c,c,hc0⟩
  have hRV (x : Fin n → VFType (M := M)) (hx : x ∈ D.carrier) : tupleRV x = t := by
    apply Eq.trans (b := tupleRV c) ?_ hcRV
    funext i
    apply Subtype.ext
    apply (CanonicalRV.encoded_eq_iff_close (x i).property (c i).property
      (fun h => hc0 i (Subtype.ext h))).mpr
    change ¬ VFValued.predV (c i) (x i - c i)
    rw [Values.presentation_compatible,not_le]
    exact hx i
  have hdim := vfDim_eq_arity_of_contains_polydisc hc hs hR
    (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) Values.presentation_compatible
    A (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) D (fun x hx => ⟨hRV x hx,Set.mem_univ _⟩)
  obtain ⟨p,hp⟩ := exists_independent_of_full_dimension hc hs hR
    (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) A
    ⟨(c,Fin.elim0),hcRV,Set.mem_univ _⟩ hdim
  refine ⟨p.val.1,p.property.1,?_⟩
  have hField : vfParameterField R = vfParameterField S :=
    vfParameterField_union_rv S _ (by rintro z ⟨i,rfl⟩; exact (t i).property)
  exact Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) =>
    AlgebraicIndependent E p.val.1) hField) hp

end IntegrationInACVF.Section7
