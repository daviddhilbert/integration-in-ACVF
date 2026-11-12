import IntegrationSection6.Subobjects

/-!
The first-factor counterpart of the predecessor's
`Section4.RVProductRightDistribIso` (MIT, pinned revision in REUSE-SURVEY.md).
Both constructions use the actual definable tagged partition.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k l n m : ℕ}

theorem rvProductDomain_left_union
    (A B : DefSet (rawRVSpace (M := M) n) S) (R : DefSet (rawRVSpace (M := M) m) S) :
    rvProductDomain (A.union B) R = (rvProductDomain A R).union (rvProductDomain B R) := by
  apply DefSet.eq_of_carrier_eq
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha | hb, r, hr, he⟩ := (mem_rvProductDomain (A.union B) R t).mp ht
    · exact Or.inl ((mem_rvProductDomain A R t).mpr ⟨a, ha, r, hr, he⟩)
    · exact Or.inr ((mem_rvProductDomain B R t).mpr ⟨a, hb, r, hr, he⟩)
  · rintro (ha | hb)
    · obtain ⟨a, ha, r, hr, he⟩ := (mem_rvProductDomain A R t).mp ha
      exact (mem_rvProductDomain (A.union B) R t).mpr ⟨a, Or.inl ha, r, hr, he⟩
    · obtain ⟨b, hb, r, hr, he⟩ := (mem_rvProductDomain B R t).mp hb
      exact (mem_rvProductDomain (A.union B) R t).mpr ⟨b, Or.inr hb, r, hr, he⟩

theorem rvProductDomain_left_disjoint
    (A B : DefSet (rawRVSpace (M := M) n) S) (R : DefSet (rawRVSpace (M := M) m) S)
    (hd : Disjoint A.carrier B.carrier) :
    Disjoint (rvProductDomain A R).carrier (rvProductDomain B R).carrier := by
  apply Set.disjoint_left.mpr
  intro t hA hB
  obtain ⟨a, ha, r, hr, he⟩ := (mem_rvProductDomain A R t).mp hA
  obtain ⟨b, hb, s, hs, hf⟩ := (mem_rvProductDomain B R t).mp hB
  have heq : (a,r) = (b,s) := by
    apply rvAppend_injective
    exact he.trans hf.symm
  have hab : a = b := congrArg Prod.fst heq
  exact Set.disjoint_left.mp hd ha (hab.symm ▸ hb)

def productLeftRestrictionSubset (U : RVObject (M := M) S k) (R : RVObject (M := M) S l)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    (rvProductDomain A R.domain).carrier ⊆ (rvProductObject U R).domain.carrier := by
  intro t ht
  obtain ⟨a, ha, r, hr, he⟩ := (mem_rvProductDomain A R.domain t).mp ht
  exact (mem_rvProductDomain U.domain R.domain t).mpr ⟨a, hA ha, r, hr, he⟩

def productLeftRestrictionIso (U : RVObject (M := M) S k) (R : RVObject (M := M) S l)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    rvProductObject (U.restrict A hA) R ≅
      (rvProductObject U R).restrict (rvProductDomain A R.domain)
        (productLeftRestrictionSubset U R A hA) := by
  apply rvIsoOfVolumePreservingBijection (Map.id (rvProductDomain A R.domain)) Function.bijective_id
  intro p
  obtain ⟨a, r, rfl⟩ := exists_rvPackPair A R.domain p
  exact (rvProductObject_value_pair U R ⟨a.val, hA a.property⟩ r).trans
    (rvProductObject_value_pair (U.restrict A hA) R a r).symm

/-- Distribution in the first factor, with degree k+l and unchanged label order. -/
def productLeftDistribIso (U V : RVObject (M := M) S k) (R : RVObject (M := M) S l) :
    rvProductObject (rvCoprodObject U V) R ≅
      rvCoprodObject (rvProductObject U R) (rvProductObject V R) := by
  let T := rvCoprodObject U V
  let X := rvProductObject T R
  let A := (rvLeftTagMap U.domain V.arity).image
  let B := (rvRightTagMap V.domain U.arity).image
  let PA := rvProductDomain A R.domain
  let PB := rvProductDomain B R.domain
  have hA : A.carrier ⊆ T.domain.carrier := fun _ h => Or.inl h
  have hB : B.carrier ⊆ T.domain.carrier := fun _ h => Or.inr h
  have hPA := productLeftRestrictionSubset T R A hA
  have hPB := productLeftRestrictionSubset T R B hB
  have hd : Disjoint PA.carrier PB.carrier :=
    rvProductDomain_left_disjoint A B R.domain (rvTaggedImages_disjoint U.domain V.domain)
  have he : (PA.union PB).carrier = X.domain.carrier := by
    change ((rvProductDomain A R.domain).union (rvProductDomain B R.domain)).carrier =
      (rvProductDomain (A.union B) R.domain).carrier
    rw [rvProductDomain_left_union]
  let eA := (productLeftRestrictionIso T R A hA).symm.trans
    (rvProductIso (rvCoprodLeftRestrictionIso U V).symm (Iso.refl R))
  let eB := (productLeftRestrictionIso T R B hB).symm.trans
    (rvProductIso (rvCoprodRightRestrictionIso U V).symm (Iso.refl R))
  exact ((rvCoprodUnionIso X PA PB hPA hPB hd).trans
    (rvIsoOfCarrierEq _ _ _ _ he (fun _ => rfl))).symm.trans (rvCoprodIso eA eB)

end IntegrationInACVF.Section6
