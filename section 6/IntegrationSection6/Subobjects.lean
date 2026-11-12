import Section4.RVProductDistributivity

/-! Definable RV subobjects and complements used by blowup loci. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

@[simp] theorem iso_inv_hom_apply (e : U ≅ V) (v : V.domain) :
    e.hom.map (e.inv.map v) = v :=
  congrArg (fun f : RVHom V V => f.map v) e.inv_hom_id

@[simp] theorem iso_hom_inv_apply (e : U ≅ V) (u : U.domain) :
    e.inv.map (e.hom.map u) = u :=
  congrArg (fun f : RVHom U U => f.map u) e.hom_inv_id

theorem iso_map_bijective (e : U ≅ V) : Function.Bijective e.hom.map :=
  ⟨(show Function.LeftInverse e.inv.map e.hom.map from iso_hom_inv_apply e).injective,
    (show Function.RightInverse e.inv.map e.hom.map from iso_inv_hom_apply e).surjective⟩

/-- Image of a definable subobject, over exactly the same parameter base. -/
def subobjectImage (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    DefSet (rawRVSpace (M := M) V.arity) S := (e.hom.map.restrict hA).image

theorem subobjectImage_subset (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    (subobjectImage e A hA).carrier ⊆ V.domain.carrier := by
  rintro _ ⟨a, rfl⟩
  exact (e.hom.map ⟨a.val, hA a.property⟩).property

/-- An arbitrary RV isomorphism restricts to its actual definable image. -/
def subobjectImageIso (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    U.restrict A hA ≅ V.restrict (subobjectImage e A hA) (subobjectImage_subset e A hA) where
  hom := e.hom.restrict A hA (subobjectImage e A hA) (subobjectImage_subset e A hA)
    (fun a => ⟨a, rfl⟩)
  inv := e.inv.restrict (subobjectImage e A hA) (subobjectImage_subset e A hA) A hA (by
    rintro ⟨v, a, ha⟩
    have he : e.hom.map ⟨a.val, hA a.property⟩ =
        ⟨v, subobjectImage_subset e A hA ⟨a, ha⟩⟩ := Subtype.ext ha
    rw [← he, iso_hom_inv_apply]
    exact a.property)
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    apply Subtype.ext
    change (e.inv.map (e.hom.map ⟨a.val,hA a.property⟩)).val = a.val
    exact congrArg Subtype.val (iso_hom_inv_apply e ⟨a.val, hA a.property⟩)
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    apply Subtype.ext
    change (e.hom.map (e.inv.map ⟨a.val,subobjectImage_subset e A hA a.property⟩)).val = a.val
    exact congrArg Subtype.val
      (iso_inv_hom_apply e ⟨a.val, subobjectImage_subset e A hA a.property⟩)

/-- The complementary definable subobject retains the original labels. -/
def complement (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) :
    DefSet (rawRVSpace (M := M) U.arity) S := U.domain.sdiff A

theorem complement_subset (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) :
    (complement U A).carrier ⊆ U.domain.carrier := fun _ h => h.1

/-- The two genuine definable pieces partition the original RV object. -/
def partitionIso (U : RVObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    rvCoprodObject (U.restrict A hA) (U.restrict (complement U A) (complement_subset U A)) ≅ U := by
  have hd : Disjoint A.carrier (complement U A).carrier := by
    apply Set.disjoint_left.mpr
    intro x hx hc
    exact hc.2 hx
  have he : (A.union (complement U A)).carrier = U.domain.carrier := by
    ext x
    constructor
    · rintro (h | h)
      · exact hA h
      · exact h.1
    · intro hx
      by_cases ha : x ∈ A.carrier
      · exact Or.inl ha
      · exact Or.inr ⟨hx, ha⟩
  exact (rvCoprodUnionIso U A (complement U A) hA (complement_subset U A) hd).trans
    (rvIsoOfCarrierEq _ _ _ _ he (fun _ => rfl))

/-- Images under an isomorphism commute with relative complements. -/
theorem subobjectImage_complement (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    (subobjectImage e (complement U A) (complement_subset U A)).carrier =
      (complement V (subobjectImage e A hA)).carrier := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(e.hom.map ⟨a.val, a.property.1⟩).property, ?_⟩
    rintro ⟨b, hb⟩
    have he : e.hom.map ⟨b.val, hA b.property⟩ = e.hom.map ⟨a.val, a.property.1⟩ :=
      Subtype.ext hb
    have hab := congrArg Subtype.val ((iso_map_bijective e).1 he)
    exact a.property.2 (hab ▸ b.property)
  · rintro ⟨hv, hn⟩
    let u := e.inv.map ⟨v, hv⟩
    have hu : u.val ∉ A.carrier := by
      intro h
      apply hn
      refine ⟨⟨u.val, h⟩, ?_⟩
      exact congrArg Subtype.val (iso_inv_hom_apply e ⟨v, hv⟩)
    refine ⟨⟨u.val, u.property, hu⟩, ?_⟩
    exact congrArg Subtype.val (iso_inv_hom_apply e ⟨v, hv⟩)

/-- Isomorphism of the complementary objects, with the actual image locus. -/
def complementImageIso (e : U ≅ V)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    U.restrict (complement U A) (complement_subset U A) ≅
      V.restrict (complement V (subobjectImage e A hA))
        (complement_subset V (subobjectImage e A hA)) :=
  (subobjectImageIso e (complement U A) (complement_subset U A)).trans
    (rvIsoOfCarrierEq _ _ _ _ (subobjectImage_complement e A hA) (fun _ => rfl))

end IntegrationInACVF.Section6
