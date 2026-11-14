import Section4.RVProductDistributivity

/-! The explicit distributivity chart, in the direction that removes
the coproduct tag after taking its product. All arities, including zero, work. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

theorem rvObjectCoprod_cases (U V : RVObject (M := M) S k)
    (x : (rvCoprodObject U V).domain) :
    (∃ u, rvCoprodLeftMap U V u = x) ∨ (∃ v, rvCoprodRightMap U V v = x) := by
  rcases x.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · exact Or.inl ⟨u,Subtype.ext hu⟩
  · exact Or.inr ⟨v,Subtype.ext hv⟩

theorem rvProductMap_pair {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) (u : U.domain) (v : V.domain) :
    rvProductMap f g (rvPackPair U.domain V.domain u v) =
      rvPackPair U'.domain V'.domain (f u) (g v) := by
  simp only [rvProductMap,Map.comp_apply,rvUnpack_pair]
  rfl

theorem rvProductMap_injective {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (rvProductMap f g) := by
  intro x y h
  apply (rvUnpack_bijective U.domain V.domain).1
  have he := congrArg (rvUnpack U'.domain V'.domain) h
  rw [rvProductMap_unpack,rvProductMap_unpack] at he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : U.domain => z.val) (hf (Subtype.ext
      (congrArg (fun z : U'.domain.prod V'.domain => z.val.1) he)))
  · exact congrArg (fun z : V.domain => z.val) (hg (Subtype.ext
      (congrArg (fun z : U'.domain.prod V'.domain => z.val.2) he)))

def rvProductCoprodFold (U : RVObject (M := M) S k) (V W : RVObject (M := M) S l) :
    RVHom (rvCoprodObject (rvProductObject U V) (rvProductObject U W))
      (rvProductObject U (rvCoprodObject V W)) :=
  rvCoprodDesc (rvProductHom (𝟙 U) (rvCoprodInl V W))
    (rvProductHom (𝟙 U) (rvCoprodInr V W))

theorem rvProductCoprodFold_left (U : RVObject (M := M) S k) (V W : RVObject (M := M) S l)
    (x : (rvProductObject U V).domain) :
    (rvProductCoprodFold U V W).map
      (rvCoprodLeftMap (rvProductObject U V) (rvProductObject U W) x) =
        rvProductMap (Map.id U.domain) (rvCoprodLeftMap V W) x :=
  congrArg (fun h : RVHom (rvProductObject U V) (rvProductObject U (rvCoprodObject V W)) => h.map x)
    (rvCoprodInl_desc _ _)

theorem rvProductCoprodFold_right (U : RVObject (M := M) S k) (V W : RVObject (M := M) S l)
    (x : (rvProductObject U W).domain) :
    (rvProductCoprodFold U V W).map
      (rvCoprodRightMap (rvProductObject U V) (rvProductObject U W) x) =
        rvProductMap (Map.id U.domain) (rvCoprodRightMap V W) x :=
  congrArg (fun h : RVHom (rvProductObject U W) (rvProductObject U (rvCoprodObject V W)) => h.map x)
    (rvCoprodInr_desc _ _)

theorem rvProductCoprodFold_bijective (U : RVObject (M := M) S k) (V W : RVObject (M := M) S l) :
    Function.Bijective (rvProductCoprodFold U V W).map := by
  have hl : Function.Injective (rvCoprodLeftMap V W) := by
    intro x y h
    exact Subtype.ext (rvLeftTag_injective W.arity (congrArg (fun z : (rvCoprodObject V W).domain => z.val) h))
  have hr : Function.Injective (rvCoprodRightMap V W) := by
    intro x y h
    exact Subtype.ext (rvRightTag_injective V.arity (congrArg (fun z : (rvCoprodObject V W).domain => z.val) h))
  have hcross (x : (rvProductObject U V).domain) (y : (rvProductObject U W).domain) :
      rvProductMap (Map.id U.domain) (rvCoprodLeftMap V W) x ≠
        rvProductMap (Map.id U.domain) (rvCoprodRightMap V W) y := by
    intro he
    have h := congrArg (fun z : (rvProductObject U (rvCoprodObject V W)).domain =>
      (rvUnpack U.domain (rvCoprodObject V W).domain z).val.2) he
    rw [rvProductMap_unpack,rvProductMap_unpack] at h
    exact rvTag_disjoint _ _ h
  constructor
  · intro x y h
    rcases rvObjectCoprod_cases (rvProductObject U V) (rvProductObject U W) x with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;>
      rcases rvObjectCoprod_cases (rvProductObject U V) (rvProductObject U W) y with ⟨b,rfl⟩ | ⟨b,rfl⟩
    · rw [rvProductCoprodFold_left,rvProductCoprodFold_left] at h
      exact congrArg (rvCoprodLeftMap (rvProductObject U V) (rvProductObject U W))
        (rvProductMap_injective _ _ Function.injective_id hl h)
    · rw [rvProductCoprodFold_left,rvProductCoprodFold_right] at h
      exact (hcross a b h).elim
    · rw [rvProductCoprodFold_right,rvProductCoprodFold_left] at h
      exact (hcross b a h.symm).elim
    · rw [rvProductCoprodFold_right,rvProductCoprodFold_right] at h
      exact congrArg (rvCoprodRightMap (rvProductObject U V) (rvProductObject U W))
        (rvProductMap_injective _ _ Function.injective_id hr h)
  · intro x
    obtain ⟨u,vw,rfl⟩ := exists_rvPackPair U.domain (rvCoprodObject V W).domain x
    rcases rvObjectCoprod_cases V W vw with ⟨v,rfl⟩ | ⟨w,rfl⟩
    · refine ⟨rvCoprodLeftMap (rvProductObject U V) (rvProductObject U W)
        (rvPackPair U.domain V.domain u v),?_⟩
      rw [rvProductCoprodFold_left,rvProductMap_pair]
      rfl
    · refine ⟨rvCoprodRightMap (rvProductObject U V) (rvProductObject U W)
        (rvPackPair U.domain W.domain u w),?_⟩
      rw [rvProductCoprodFold_right,rvProductMap_pair]
      rfl

end IntegrationInACVF.Section7
