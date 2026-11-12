import IntegrationSection6.ElementaryRestrictions
import IntegrationSection6.ElementaryPacking

/-! Product geometry for the multiplicative compatibility in Lemma 6.8. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k l : ℕ}

theorem mapInverse_bijective {L : Language} {N : Type} [L.Structure N]
    {P Q : Space L N} {T : Set N} {A : DefSet P T} {B : DefSet Q T}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (f.inverse hf) :=
  ⟨(show Function.LeftInverse f (f.inverse hf) from Map.apply_inverse f hf).injective,
    (show Function.RightInverse f (f.inverse hf) from Map.inverse_apply f hf).surjective⟩

/-- Scaling a coordinate of the first label block commutes with concatenation. -/
theorem blowupValue_append (i : Fin k) (u : Fin k → CanonicalRV.RVSort M)
    (v : Fin l → CanonicalRV.RVSort M) (s : CanonicalRV.RVSort M) :
    blowupValue (Fin.castAdd l i) (rvAppend u v) s = rvAppend (blowupValue i u s) v := by
  funext a
  refine Fin.addCases (fun j => ?_) (fun j => ?_) a
  · have he : (Fin.castAdd l j = Fin.castAdd l i) ↔ j = i := by
      constructor
      · intro h
        exact Fin.castAdd_injective k l h
      · exact congrArg (Fin.castAdd l)
    simp only [blowupValue, rvAppend, Fin.append_left, he]
  · have hn : Fin.natAdd k j ≠ Fin.castAdd l i := by
      intro h
      have he := congrArg Fin.val h
      have hi := i.isLt
      change k + j.val = i.val at he
      omega
    simp only [blowupValue, hn, ite_false, rvAppend, Fin.append_right]

/-- Admissibility is preserved after adding an unrelated RV factor. -/
theorem Admissible.product {U : RVObject (M := M) S k} {i : Fin k}
    (h : Admissible U i) (R : RVObject (M := M) S l) :
    Admissible (rvProductObject U R) (Fin.castAdd l i) where
  nonzero a := by
    obtain ⟨u, r, rfl⟩ := exists_rvPackPair U.domain R.domain a
    simpa only [rvProductObject_value_pair, rvAppend, Fin.append_left] using h.nonzero u
  algebraic a := by
    obtain ⟨u, r, rfl⟩ := exists_rvPackPair U.domain R.domain a
    rw [rvProductObject_value_pair]
    change AlgebraicAt (coordinateBase S (Fin.castAdd l i) (rvAppend (U.value u) (R.value r)))
      .rv ((rvAppend (U.value u) (R.value r)) (Fin.castAdd l i)).val
    simp only [rvAppend, Fin.append_left]
    apply (h.algebraic u).mono
    rintro x (hx | ⟨j, hj, he⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨Fin.castAdd l j, ?_, ?_⟩
      · intro hji
        exact hj (Fin.castAdd_injective k l hji)
      · simpa only [Fin.append_left] using he

/-- Reassociate the three packed domain blocks (U,R,s) as (U,s,R). -/
def elementaryProductMap (U : RVObject (M := M) S k) (R : RVObject (M := M) S l)
    (i : Fin k) : Map (elementary (rvProductObject U R) (Fin.castAdd l i)).domain
      (rvProductObject (elementary U i) R).domain :=
  (rvPack (elementary U i).domain R.domain).toImage.comp
    ((Map.prodMap (rvPack U.domain (positiveRV S)).toImage (Map.id R.domain)).comp
      (((Map.prodAssoc U.domain (positiveRV S) R.domain).inverse
          (Map.prodAssoc_bijective U.domain (positiveRV S) R.domain)).comp
        ((Map.prodMap (Map.id U.domain) (Map.prodSwap R.domain (positiveRV S))).comp
          ((Map.prodAssoc U.domain R.domain (positiveRV S)).comp
            ((Map.prodMap (rvUnpack U.domain R.domain) (Map.id (positiveRV S))).comp
              (rvUnpack (rvProductObject U R).domain (positiveRV S)))))))

theorem elementaryProductMap_bijective (U : RVObject (M := M) S k)
    (R : RVObject (M := M) S l) (i : Fin k) :
    Function.Bijective (elementaryProductMap U R i) :=
  (rvPackToImage_bijective (elementary U i).domain R.domain).comp
    ((Map.prodMap_bijective _ _ (rvPackToImage_bijective U.domain (positiveRV S))
        Function.bijective_id).comp
      ((mapInverse_bijective _ (Map.prodAssoc_bijective U.domain (positiveRV S) R.domain)).comp
        ((Map.prodMap_bijective _ _ Function.bijective_id
            (Map.prodSwap_bijective R.domain (positiveRV S))).comp
          ((Map.prodAssoc_bijective U.domain R.domain (positiveRV S)).comp
            ((Map.prodMap_bijective _ _ (rvUnpack_bijective U.domain R.domain)
                Function.bijective_id).comp
              (rvUnpack_bijective (rvProductObject U R).domain (positiveRV S)))))))

theorem elementaryProductMap_pair (U : RVObject (M := M) S k)
    (R : RVObject (M := M) S l) (i : Fin k) (u : U.domain) (r : R.domain)
    (s : positiveRV (M := M) S) :
    elementaryProductMap U R i
      (rvPackPair (rvProductObject U R).domain (positiveRV S)
        (rvPackPair U.domain R.domain u r) s) =
      rvPackPair (elementary U i).domain R.domain (rvPackPair U.domain (positiveRV S) u s) r := by
  have hi := Map.inverse_apply (Map.prodAssoc U.domain (positiveRV S) R.domain)
    (Map.prodAssoc_bijective U.domain (positiveRV S) R.domain)
    ⟨((u.val, s.val), r.val), ⟨u.property, s.property⟩, r.property⟩
  have hswap : Map.prodSwap R.domain (positiveRV S)
      ⟨(r.val,s.val),r.property,s.property⟩ =
        ⟨(s.val,r.val),s.property,r.property⟩ := rfl
  have hswap2 : (Map.prodMap (Map.id U.domain) (Map.prodSwap R.domain (positiveRV S)))
      ⟨(u.val,r.val,s.val),u.property,r.property,s.property⟩ =
        ⟨(u.val,s.val,r.val),u.property,s.property,r.property⟩ := rfl
  simp only [elementaryProductMap, Map.comp_apply, rvPackPair, rvUnpack_pack,
    Map.prodMap_mk, Map.prodAssoc_mk, Map.id_apply, hswap, hswap2] at hi ⊢
  rw [hi]
  rfl

/-- The elementary blowup of a product is the product of the elementary
blowup, with a definable permutation of the packed domain blocks. -/
def elementaryProductIso (U : RVObject (M := M) S k) (R : RVObject (M := M) S l)
    (i : Fin k) : elementary (rvProductObject U R) (Fin.castAdd l i) ≅
      rvProductObject (elementary U i) R := by
  apply rvIsoOfVolumePreservingBijection (elementaryProductMap U R i)
    (elementaryProductMap_bijective U R i)
  intro a
  obtain ⟨p, s, rfl⟩ := exists_rvPackPair (rvProductObject U R).domain (positiveRV S) a
  obtain ⟨u, r, rfl⟩ := exists_rvPackPair U.domain R.domain p
  rw [elementaryProductMap_pair, rvProductObject_value_pair, elementary_value,
    elementaryProjection_pair, elementaryParameter_pair, elementary_value,
    elementaryProjection_pair, elementaryParameter_pair, rvProductObject_value_pair]
  exact (blowupValue_append i (U.value u) (R.value r) (s.val 0)).symm

end IntegrationInACVF.Section6
