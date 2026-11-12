import IntegrationSection6.Blowups
import IntegrationSection6.ElementaryRestrictions

/-!
# Coproduct presentations of actual blowups

The equivalence with a single elementary replacement in a coproduct is proved
using actual definable loci and their images. It does not replace Definition
6.1 by a freely generated relation.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- The complement of the first tagged summand is exactly the second. -/
theorem coprod_left_complement (C R : RVObject (M := M) S k) :
    (complement (rvCoprodObject C R) (rvLeftTagMap C.domain R.arity).image).carrier =
      (rvRightTagMap R.domain C.arity).image.carrier := by
  ext x
  constructor
  · rintro ⟨hl | hr, hn⟩
    · exact False.elim (hn hl)
    · exact hr
  · intro hr
    refine ⟨Or.inr hr, ?_⟩
    intro hl
    exact Set.disjoint_left.mp (rvTaggedImages_disjoint C.domain R.domain) hl hr

def coprodComplementIso (C R : RVObject (M := M) S k) :
    (rvCoprodObject C R).restrict
      (complement (rvCoprodObject C R) (rvLeftTagMap C.domain R.arity).image)
      (complement_subset _ _) ≅ R :=
  (rvIsoOfCarrierEq _ _ _ _ (coprod_left_complement C R) (fun _ => rfl)).trans
    (rvCoprodRightRestrictionIso C R).symm

/-- Every elementary replacement in an isomorphic coproduct presentation
is a blowup at a genuine definable subobject of the original object. -/
def Blowup.of_split {U V C R : RVObject (M := M) S k}
    (i : Fin k) (hC : Admissible C i) (e : U ≅ rvCoprodObject C R)
    (f : V ≅ rvCoprodObject (elementary C i) R) : Blowup U V := by
  let W := rvCoprodObject C R
  let A := (rvLeftTagMap C.domain R.arity).image
  have hA : A.carrier ⊆ W.domain.carrier := fun _ h => Or.inl h
  let er : R ≅ U.restrict (complement U (subobjectImage e.symm A hA))
      (complement_subset _ _) :=
    (coprodComplementIso C R).symm.trans (complementImageIso e.symm A hA)
  exact {
    center := C
    coordinate := i
    admissible := hC
    locus := subobjectImage e.symm A hA
    contained := subobjectImage_subset e.symm A hA
    chart := (rvCoprodLeftRestrictionIso C R).trans (subobjectImageIso e.symm A hA)
    result := f.trans (rvCoprodIso (Iso.refl _) er) }

/-- Conversely, the original locus and its complement give the coproduct
presentation of a general blowup. -/
def Blowup.source_split {U V : RVObject (M := M) S k} (h : Blowup U V) :
    U ≅ rvCoprodObject h.center
      (U.restrict (complement U h.locus) (complement_subset U h.locus)) :=
  ((rvCoprodIso h.chart (Iso.refl _)).trans (partitionIso U h.locus h.contained)).symm

/-- Characterization of a single actual blowup by elementary replacement
of a coproduct summand, retaining its admissibility hypothesis. -/
theorem blowup_iff_split (U V : RVObject (M := M) S k) :
    Nonempty (Blowup U V) ↔
      ∃ (C R : RVObject (M := M) S k) (i : Fin k), Admissible C i ∧
        Nonempty (U ≅ rvCoprodObject C R) ∧
        Nonempty (V ≅ rvCoprodObject (elementary C i) R) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.center, U.restrict (complement U h.locus) (complement_subset U h.locus),
      h.coordinate, h.admissible, ⟨h.source_split⟩, ⟨h.result⟩⟩
  · rintro ⟨C, R, i, hC, ⟨e⟩, ⟨f⟩⟩
    exact ⟨Blowup.of_split i hC e f⟩

end IntegrationInACVF.Section6
