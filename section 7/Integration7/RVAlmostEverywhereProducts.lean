import Integration7.RVProductDimension

/-! Product exceptional sets are bounded by the factors' volume
degrees, rather than by the number of auxiliary label coordinates. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b n m : ℕ}

theorem finiteVolumeDomain_dim_le (U : RVFiniteObject (M := M) S n) : rvDim U.obj.domain ≤ n :=
  (rvDim_le_iff _ _).mpr ⟨n, le_rfl, U.obj.volume, U.property⟩

theorem RVAlmostEverywhere.product_right_bound
    {A : DefSet (rawRVSpace (M := M) a) S} (B : DefSet (rawRVSpace (M := M) b) S)
    (hB : rvDim B ≤ m) {P : A → Prop} (hP : RVAlmostEverywhere A n P) :
    RVAlmostEverywhere (rvProductDomain A B) (n + m)
      (fun u => P (Map.prodFst A B (rvUnpack A B u))) := by
  obtain ⟨D, hDA, hd, hP⟩ := hP
  let E := rvProductDomain D B
  have hEA : E.carrier ⊆ (rvProductDomain A B).carrier := by
    rintro z ⟨p, rfl⟩
    exact ⟨⟨p.val, hDA p.property.1, p.property.2⟩, rfl⟩
  have hdim : rvDim E < n + m :=
    (rvDim_productDomain_le D B).trans_lt
      ((Nat.add_le_add_left hB (rvDim D)).trans_lt (Nat.add_lt_add_right hd m))
  refine ⟨E, hEA, hdim, ?_⟩
  intro u hu
  apply hP
  intro hD
  apply hu
  exact ⟨⟨(rvUnpack A B u).val, hD, (rvUnpack A B u).property.2⟩,
    congrArg (fun p : rvProductDomain A B => p.val) (rvPack_unpack A B u)⟩

theorem RVAlmostEverywhere.product_left_bound
    (A : DefSet (rawRVSpace (M := M) a) S) {B : DefSet (rawRVSpace (M := M) b) S}
    (hA : rvDim A ≤ n) {Q : B → Prop} (hQ : RVAlmostEverywhere B m Q) :
    RVAlmostEverywhere (rvProductDomain A B) (n + m)
      (fun u => Q (Map.prodSnd A B (rvUnpack A B u))) := by
  obtain ⟨D, hDB, hd, hQ⟩ := hQ
  let E := rvProductDomain A D
  have hEA : E.carrier ⊆ (rvProductDomain A B).carrier := by
    rintro z ⟨p, rfl⟩
    exact ⟨⟨p.val, p.property.1, hDB p.property.2⟩, rfl⟩
  have hdim : rvDim E < n + m :=
    (rvDim_productDomain_le A D).trans_lt
      ((Nat.add_le_add_right hA (rvDim D)).trans_lt (Nat.add_lt_add_left hd n))
  refine ⟨E, hEA, hdim, ?_⟩
  intro u hu
  apply hQ
  intro hD
  apply hu
  exact ⟨⟨(rvUnpack A B u).val, (rvUnpack A B u).property.1, hD⟩,
    congrArg (fun p : rvProductDomain A B => p.val) (rvPack_unpack A B u)⟩

theorem RVAlmostEverywhere.product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)}
    {B : DefSet (rawRVSpace (M := M) b) (C.base : Set M)}
    (hA : rvDim A ≤ n) (hB : rvDim B ≤ m) {P : A → Prop} {Q : B → Prop}
    (hP : RVAlmostEverywhere A n P) (hQ : RVAlmostEverywhere B m Q) :
    RVAlmostEverywhere (rvProductDomain A B) (n + m) (fun u =>
      P (Map.prodFst A B (rvUnpack A B u)) ∧ Q (Map.prodSnd A B (rvUnpack A B u))) :=
  (hP.product_right_bound B hB).and hc C (hQ.product_left_bound A hA)

end IntegrationInACVF.Section7
