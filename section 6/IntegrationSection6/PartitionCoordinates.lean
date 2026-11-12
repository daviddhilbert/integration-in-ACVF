import IntegrationSection6.Subobjects

/-! Coordinate formulas for the actual coproduct partition isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

theorem partitionIso_left (U : RVObject (M := M) S n)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    (a : A) :
    ((partitionIso U A hA).hom.map
      (rvCoprodLeftMap (U.restrict A hA) (U.restrict (complement U A) (complement_subset U A)) a)).val = a.val := by
  let E := complement U A
  have hd : Disjoint A.carrier E.carrier := by
    exact Set.disjoint_left.mpr (fun x hx he => he.2 hx)
  have h := (rvCoprodIsColimit (U.restrict A hA) (U.restrict E (complement_subset U A))).comp_coconePointUniqueUpToIso_hom
    (rvUnionIsColimit U A E hA (complement_subset U A) hd) ⟨WalkingPair.left⟩
  exact congrArg (fun f : RVHom (U.restrict A hA) (U.restrict (A.union E) (rvUnionSubset U A E hA (complement_subset U A))) => (f.map a).val) h

theorem partitionIso_right (U : RVObject (M := M) S n)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier)
    (a : complement U A) :
    ((partitionIso U A hA).hom.map
      (rvCoprodRightMap (U.restrict A hA) (U.restrict (complement U A) (complement_subset U A)) a)).val = a.val := by
  let E := complement U A
  have hd : Disjoint A.carrier E.carrier := by
    exact Set.disjoint_left.mpr (fun x hx he => he.2 hx)
  have h := (rvCoprodIsColimit (U.restrict A hA) (U.restrict E (complement_subset U A))).comp_coconePointUniqueUpToIso_hom
    (rvUnionIsColimit U A E hA (complement_subset U A) hd) ⟨WalkingPair.right⟩
  exact congrArg (fun f : RVHom (U.restrict E (complement_subset U A)) (U.restrict (A.union E) (rvUnionSubset U A E hA (complement_subset U A))) => (f.map a).val) h

end IntegrationInACVF.Section6
