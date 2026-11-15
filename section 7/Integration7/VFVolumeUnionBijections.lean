import Integration7.VFVolumeUnionMaps
import Integration7.RawVFVolumeComposition

/-! Actual bijections glue over disjoint source and target domains,
with the original volume forms on both pieces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.union
    (U V : PositiveVFVolumeObject (M := M) S k) (ha : V.arity = U.arity) :
    PositiveVFVolumeObject (M := M) S k := by
  cases U with | mk a A hA ω =>
    cases V with | mk b B hB π =>
      dsimp at ha
      subst b
      exact ⟨a,A.union B,fun x => (hA x).union (hB x),ω.union π⟩

theorem preservesVFVolume_inclusion
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n a : ℕ}
    (hn : 0 < n)
    {A B : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    (hAB : A.carrier ⊆ B.carrier) (ω : VolumeForm A) (π : VolumeForm B)
    (hω : ∀ p : A, ω.value p = π.value (Map.inclusion hAB p)) :
    PreservesVFVolume ω π (Map.inclusion hAB) := by
  apply (vfJacobianOne_of_preservesVF hc C hn (Map.inclusion hAB) (fun _ => rfl)).mono
  intro p hJ
  exact ⟨1,hJ,by rw [RVOperations.rv_one,mul_one]; exact hω p⟩

def unionMixedMap {n a b : ℕ}
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    {D E : DefSet (rawMixedSpace (M := M) n b) S}
    (f : Map A D) (g : Map B E) : Map (A.union B) (D.union E) :=
  ((Map.inclusion Set.subset_union_left).comp f).union
    ((Map.inclusion Set.subset_union_right).comp g)

theorem unionMixedMap_bijective {n a b : ℕ}
    {A B : DefSet (rawMixedSpace (M := M) n a) S}
    {D E : DefSet (rawMixedSpace (M := M) n b) S}
    (hAB : Disjoint A.carrier B.carrier) (hDE : Disjoint D.carrier E.carrier)
    (f : Map A D) (g : Map B E) (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (unionMixedMap f g) := by
  let F : Map A (D.union E) := (Map.inclusion Set.subset_union_left).comp f
  let G : Map B (D.union E) := (Map.inclusion Set.subset_union_right).comp g
  change Function.Bijective (F.union G)
  constructor
  · rintro ⟨p,hp⟩ ⟨q,hq⟩ he
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · rw [Map.union_on_left F G ⟨p,hp⟩,Map.union_on_left F G ⟨q,hq⟩] at he
      have hv := congrArg (fun r : D.union E => r.val) he
      have heq : f ⟨p,hp⟩ = f ⟨q,hq⟩ := Subtype.ext hv
      exact Subtype.ext (congrArg (fun r : A => r.val) (hf.1 heq))
    · rw [Map.union_on_left F G ⟨p,hp⟩,Map.union_on_right F G hAB ⟨q,hq⟩] at he
      have hv := congrArg Subtype.val he
      exact False.elim (Set.disjoint_left.mp hDE (f ⟨p,hp⟩).property
        (hv.symm ▸ (g ⟨q,hq⟩).property))
    · rw [Map.union_on_right F G hAB ⟨p,hp⟩,Map.union_on_left F G ⟨q,hq⟩] at he
      have hv := congrArg Subtype.val he
      exact False.elim (Set.disjoint_left.mp hDE (f ⟨q,hq⟩).property
        (hv ▸ (g ⟨p,hp⟩).property))
    · rw [Map.union_on_right F G hAB ⟨p,hp⟩,Map.union_on_right F G hAB ⟨q,hq⟩] at he
      have hv := congrArg (fun r : D.union E => r.val) he
      have heq : g ⟨p,hp⟩ = g ⟨q,hq⟩ := Subtype.ext hv
      exact Subtype.ext (congrArg (fun r : B => r.val) (hg.1 heq))
  · rintro ⟨p,hp⟩
    rcases hp with hp | hp
    · obtain ⟨q,hq⟩ := hf.2 ⟨p,hp⟩
      refine ⟨⟨q.val,Or.inl q.property⟩,?_⟩
      rw [Map.union_on_left]
      have hv := congrArg (fun r : D => r.val) hq
      exact Subtype.ext hv
    · obtain ⟨q,hq⟩ := hg.2 ⟨p,hp⟩
      refine ⟨⟨q.val,Or.inr q.property⟩,?_⟩
      rw [Map.union_on_right F G hAB]
      have hv := congrArg (fun r : E => r.val) hq
      exact Subtype.ext hv

theorem preservesVFVolume_unionMixedMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n a b : ℕ}
    (hn : 0 < n)
    {A B : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {D E : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (hAB : Disjoint A.carrier B.carrier) (hDE : Disjoint D.carrier E.carrier)
    (f : Map A D) (g : Map B E) (hf : Function.Injective f) (hg : Function.Injective g)
    (ω : VolumeForm A) (η : VolumeForm B) (π : VolumeForm D) (ρ : VolumeForm E)
    (hF : PreservesVFVolume ω π f) (hG : PreservesVFVolume η ρ g) :
    PreservesVFVolume (ω.union η) (π.union ρ) (unionMixedMap f g) := by
  apply preservesVFVolume_union hc C hn hAB
  · exact preservesVFVolume_comp hc C hn ω π (π.union ρ) f
      (Map.inclusion Set.subset_union_left) hf hF
      (preservesVFVolume_inclusion hc C hn _ π (π.union ρ)
        (fun p => (VolumeForm.union_value_left π ρ p).symm))
  · exact preservesVFVolume_comp hc C hn η ρ (π.union ρ) g
      (Map.inclusion Set.subset_union_right) hg hG
      (preservesVFVolume_inclusion hc C hn _ ρ (π.union ρ)
        (fun p => (VolumeForm.union_value_right π ρ hDE p).symm))

end IntegrationInACVF.Section7
