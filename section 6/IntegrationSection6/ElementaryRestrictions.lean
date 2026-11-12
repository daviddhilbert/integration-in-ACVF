import IntegrationSection6.ElementaryIsomorphism
import IntegrationSection6.Subobjects

/-! Elementary blowups commute with definable partition into subobjects. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

theorem Admissible.restrict {i : Fin k} (h : Admissible U i)
    (A : DefSet (rawRVSpace (M := M) U.arity) S) (hA : A.carrier ⊆ U.domain.carrier) :
    Admissible (U.restrict A hA) i where
  nonzero a := h.nonzero ⟨a.val, hA a.property⟩
  algebraic a := h.algebraic ⟨a.val, hA a.property⟩

theorem elementaryMap_injective (i j : Fin k) (f : Map U.domain V.domain)
    (hf : Function.Injective f) : Function.Injective (elementaryMap i j f) := by
  intro a b he
  have hp := congrArg (elementaryProjection V j) he
  rw [elementaryMap_projection, elementaryMap_projection] at hp
  have hq := congrArg (elementaryParameter V j) he
  rw [elementaryMap_parameter, elementaryMap_parameter] at hq
  apply (rvUnpack_bijective U.domain (positiveRV S)).1
  exact Subtype.ext (Prod.ext (congrArg Subtype.val (hf hp)) (congrArg Subtype.val hq))

variable (U) (i : Fin k) (A : DefSet (rawRVSpace (M := M) U.arity) S)
    (hA : A.carrier ⊆ U.domain.carrier)

def elementarySubobjectMap :
    Map (elementary (U.restrict A hA) i).domain (elementary U i).domain :=
  elementaryMap i i (Map.inclusion hA)

theorem elementarySubobjectMap_injective : Function.Injective (elementarySubobjectMap U i A hA) :=
  elementaryMap_injective (U := U.restrict A hA) (V := U) i i (Map.inclusion hA) (by
    intro a b he
    exact Subtype.ext (congrArg (fun x : U.domain => x.val) he))

def elementarySubobject : DefSet (rawRVSpace (M := M) (U.arity + 1)) S :=
  (elementarySubobjectMap U i A hA).image

theorem elementarySubobject_subset :
    (elementarySubobject U i A hA).carrier ⊆ (elementary U i).domain.carrier := by
  rintro _ ⟨a, rfl⟩
  exact (elementarySubobjectMap U i A hA a).property

/-- A direct characterization of the actual blowup subobject image. -/
theorem mem_elementarySubobject (a : (elementary U i).domain) :
    a.val ∈ (elementarySubobject U i A hA).carrier ↔
      (elementaryProjection U i a).val ∈ A.carrier := by
  constructor
  · rintro ⟨b, hb⟩
    have he : elementarySubobjectMap U i A hA b = a := Subtype.ext hb
    have hp := congrArg (elementaryProjection U i) he
    rw [elementarySubobjectMap, elementaryMap_projection] at hp
    exact (congrArg Subtype.val hp) ▸ (elementaryProjection (U.restrict A hA) i b).property
  · intro ha
    let p : A.prod (positiveRV (M := M) S) :=
      ⟨((elementaryProjection U i a).val, (elementaryParameter U i a).val),
        ha, (elementaryParameter U i a).property⟩
    let b := (rvPack A (positiveRV S)).toImage p
    refine ⟨b, ?_⟩
    have he : elementarySubobjectMap U i A hA b = a := by
      apply (rvUnpack_bijective U.domain (positiveRV S)).1
      change rvUnpack U.domain (positiveRV S)
          ((rvPack U.domain (positiveRV S)).toImage
            (Map.prodMap (Map.inclusion hA) (Map.id (positiveRV S))
              (rvUnpack A (positiveRV S) ((rvPack A (positiveRV S)).toImage p)))) = _
      rw [rvUnpack_pack, rvUnpack_pack]
      rfl
    exact congrArg Subtype.val he

def elementarySubobjectIso : elementary (U.restrict A hA) i ≅
    (elementary U i).restrict (elementarySubobject U i A hA)
      (elementarySubobject_subset U i A hA) := by
  let f := elementarySubobjectMap U i A hA
  have hf : Function.Bijective f.toImage := by
    constructor
    · intro a b he
      apply elementarySubobjectMap_injective U i A hA
      apply Subtype.ext
      exact congrArg (fun x : f.image => x.val) he
    · rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩
  apply rvIsoOfVolumePreservingBijection f.toImage hf
  intro a
  change (elementary U i).value (elementarySubobjectMap U i A hA a) = _
  rw [elementary_value, elementarySubobjectMap, elementaryMap_projection,
    elementaryMap_parameter, elementary_value]
  rfl

/-- Distribution over a definable partition, with the original coordinate
and its labels retained on both pieces. This supports the local diamond. -/
def elementaryPartitionIso :
    rvCoprodObject (elementary (U.restrict A hA) i)
      (elementary (U.restrict (complement U A) (complement_subset U A)) i) ≅ elementary U i := by
  let X := elementarySubobject U i A hA
  let Y := elementarySubobject U i (complement U A) (complement_subset U A)
  have hX := elementarySubobject_subset U i A hA
  have hY := elementarySubobject_subset U i (complement U A) (complement_subset U A)
  have hd : Disjoint X.carrier Y.carrier := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    let a : (elementary U i).domain := ⟨x, hX hx⟩
    have hp := (mem_elementarySubobject U i A hA a).mp hx
    exact ((mem_elementarySubobject U i (complement U A) (complement_subset U A) a).mp hy).2 hp
  have he : (X.union Y).carrier = (elementary U i).domain.carrier := by
    ext x
    constructor
    · rintro (hx | hy)
      · exact hX hx
      · exact hY hy
    · intro hx
      let a : (elementary U i).domain := ⟨x, hx⟩
      by_cases ha : (elementaryProjection U i a).val ∈ A.carrier
      · exact Or.inl ((mem_elementarySubobject U i A hA a).mpr ha)
      · exact Or.inr ((mem_elementarySubobject U i (complement U A)
          (complement_subset U A) a).mpr ⟨(elementaryProjection U i a).property, ha⟩)
  exact (rvCoprodIso (elementarySubobjectIso U i A hA)
      (elementarySubobjectIso U i (complement U A) (complement_subset U A))).trans
    ((rvCoprodUnionIso (elementary U i) X Y hX hY hd).trans
      (rvIsoOfCarrierEq _ _ _ _ he (fun _ => rfl)))

end IntegrationInACVF.Section6
