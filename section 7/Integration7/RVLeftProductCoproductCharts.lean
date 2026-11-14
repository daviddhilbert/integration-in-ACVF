import Integration7.RVProductCoproductCharts

/-! Explicit left distributivity without exchanging volume coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def rvLeftProductCoprodFold (U V : RVObject (M := M) S k) (W : RVObject (M := M) S l) :
    RVHom (rvCoprodObject (rvProductObject U W) (rvProductObject V W))
      (rvProductObject (rvCoprodObject U V) W) :=
  rvCoprodDesc (rvProductHom (rvCoprodInl U V) (𝟙 W))
    (rvProductHom (rvCoprodInr U V) (𝟙 W))

theorem rvLeftProductCoprodFold_left (U V : RVObject (M := M) S k) (W : RVObject (M := M) S l)
    (x : (rvProductObject U W).domain) :
    (rvLeftProductCoprodFold U V W).map
      (rvCoprodLeftMap (rvProductObject U W) (rvProductObject V W) x) =
        rvProductMap (rvCoprodLeftMap U V) (Map.id W.domain) x :=
  congrArg (fun h : RVHom (rvProductObject U W) (rvProductObject (rvCoprodObject U V) W) => h.map x)
    (rvCoprodInl_desc _ _)

theorem rvLeftProductCoprodFold_right (U V : RVObject (M := M) S k) (W : RVObject (M := M) S l)
    (x : (rvProductObject V W).domain) :
    (rvLeftProductCoprodFold U V W).map
      (rvCoprodRightMap (rvProductObject U W) (rvProductObject V W) x) =
        rvProductMap (rvCoprodRightMap U V) (Map.id W.domain) x :=
  congrArg (fun h : RVHom (rvProductObject V W) (rvProductObject (rvCoprodObject U V) W) => h.map x)
    (rvCoprodInr_desc _ _)

theorem rvLeftProductCoprodFold_bijective (U V : RVObject (M := M) S k) (W : RVObject (M := M) S l) :
    Function.Bijective (rvLeftProductCoprodFold U V W).map := by
  have hl : Function.Injective (rvCoprodLeftMap U V) := by
    intro x y h
    exact Subtype.ext (rvLeftTag_injective V.arity (congrArg (fun z : (rvCoprodObject U V).domain => z.val) h))
  have hr : Function.Injective (rvCoprodRightMap U V) := by
    intro x y h
    exact Subtype.ext (rvRightTag_injective U.arity (congrArg (fun z : (rvCoprodObject U V).domain => z.val) h))
  have hcross (x : (rvProductObject U W).domain) (y : (rvProductObject V W).domain) :
      rvProductMap (rvCoprodLeftMap U V) (Map.id W.domain) x ≠
        rvProductMap (rvCoprodRightMap U V) (Map.id W.domain) y := by
    intro he
    have h := congrArg (fun z : (rvProductObject (rvCoprodObject U V) W).domain =>
      (rvUnpack (rvCoprodObject U V).domain W.domain z).val.1) he
    rw [rvProductMap_unpack,rvProductMap_unpack] at h
    exact rvTag_disjoint _ _ h
  constructor
  · intro x y h
    rcases rvObjectCoprod_cases (rvProductObject U W) (rvProductObject V W) x with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;>
      rcases rvObjectCoprod_cases (rvProductObject U W) (rvProductObject V W) y with ⟨b,rfl⟩ | ⟨b,rfl⟩
    · rw [rvLeftProductCoprodFold_left,rvLeftProductCoprodFold_left] at h
      exact congrArg (rvCoprodLeftMap (rvProductObject U W) (rvProductObject V W))
        (rvProductMap_injective _ _ hl Function.injective_id h)
    · rw [rvLeftProductCoprodFold_left,rvLeftProductCoprodFold_right] at h
      exact (hcross a b h).elim
    · rw [rvLeftProductCoprodFold_right,rvLeftProductCoprodFold_left] at h
      exact (hcross b a h.symm).elim
    · rw [rvLeftProductCoprodFold_right,rvLeftProductCoprodFold_right] at h
      exact congrArg (rvCoprodRightMap (rvProductObject U W) (rvProductObject V W))
        (rvProductMap_injective _ _ hr Function.injective_id h)
  · intro x
    obtain ⟨uv,w,rfl⟩ := exists_rvPackPair (rvCoprodObject U V).domain W.domain x
    rcases rvObjectCoprod_cases U V uv with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · refine ⟨rvCoprodLeftMap (rvProductObject U W) (rvProductObject V W)
        (rvPackPair U.domain W.domain u w),?_⟩
      rw [rvLeftProductCoprodFold_left,rvProductMap_pair]
      rfl
    · refine ⟨rvCoprodRightMap (rvProductObject U W) (rvProductObject V W)
        (rvPackPair V.domain W.domain v w),?_⟩
      rw [rvLeftProductCoprodFold_right,rvProductMap_pair]
      rfl

end IntegrationInACVF.Section7
