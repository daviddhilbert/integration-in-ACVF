import Integration7.ExplicitRVCoproductIso

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def rvCoprodSwapExplicit (U V : RVObject (M := M) S k) :
    rvCoprodObject U V ≅ rvCoprodObject V U where
  hom := rvCoprodDesc (rvCoprodInr V U) (rvCoprodInl V U)
  inv := rvCoprodDesc (rvCoprodInr U V) (rvCoprodInl U V)
  hom_inv_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, rvCoprodInr_desc, Category.comp_id]
    · rw [← Category.assoc, rvCoprodInr_desc, rvCoprodInl_desc, Category.comp_id]
  inv_hom_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, rvCoprodInr_desc, Category.comp_id]
    · rw [← Category.assoc, rvCoprodInr_desc, rvCoprodInl_desc, Category.comp_id]

theorem rvCoprodSwapExplicit_left (U V : RVObject (M := M) S k) (u : U.domain) :
    (rvCoprodSwapExplicit U V).hom.map (rvCoprodLeftMap U V u) = rvCoprodRightMap V U u :=
  congrArg (fun h : RVHom U (rvCoprodObject V U) => h.map u)
    (rvCoprodInl_desc (rvCoprodInr V U) (rvCoprodInl V U))

theorem rvCoprodSwapExplicit_right (U V : RVObject (M := M) S k) (v : V.domain) :
    (rvCoprodSwapExplicit U V).hom.map (rvCoprodRightMap U V v) = rvCoprodLeftMap V U v :=
  congrArg (fun h : RVHom V (rvCoprodObject V U) => h.map v)
    (rvCoprodInr_desc (rvCoprodInr V U) (rvCoprodInl V U))

def rvCoprodAssocExplicit (U V W : RVObject (M := M) S k) :
    rvCoprodObject (rvCoprodObject U V) W ≅ rvCoprodObject U (rvCoprodObject V W) where
  hom := rvCoprodDesc
    (rvCoprodDesc (rvCoprodInl U (rvCoprodObject V W))
      (rvCoprodInl V W ≫ rvCoprodInr U (rvCoprodObject V W)))
    (rvCoprodInr V W ≫ rvCoprodInr U (rvCoprodObject V W))
  inv := rvCoprodDesc
    (rvCoprodInl U V ≫ rvCoprodInl (rvCoprodObject U V) W)
    (rvCoprodDesc (rvCoprodInr U V ≫ rvCoprodInl (rvCoprodObject U V) W)
      (rvCoprodInr (rvCoprodObject U V) W))
  hom_inv_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, Category.comp_id]
      apply rvCoprod_hom_ext
      · rw [← Category.assoc, rvCoprodInl_desc, rvCoprodInl_desc]
      · rw [← Category.assoc, rvCoprodInr_desc, Category.assoc,
          rvCoprodInr_desc, rvCoprodInl_desc]
    · rw [← Category.assoc, rvCoprodInr_desc, Category.assoc,
        rvCoprodInr_desc, rvCoprodInr_desc, Category.comp_id]
  inv_hom_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, Category.assoc,
        rvCoprodInl_desc, rvCoprodInl_desc, Category.comp_id]
    · rw [← Category.assoc, rvCoprodInr_desc, Category.comp_id]
      apply rvCoprod_hom_ext
      · rw [← Category.assoc, rvCoprodInl_desc, Category.assoc,
          rvCoprodInl_desc, rvCoprodInr_desc]
      · rw [← Category.assoc, rvCoprodInr_desc, rvCoprodInr_desc]

theorem rvCoprodAssocExplicit_left (U V W : RVObject (M := M) S k) (u : U.domain) :
    (rvCoprodAssocExplicit U V W).hom.map
      (rvCoprodLeftMap (rvCoprodObject U V) W (rvCoprodLeftMap U V u)) =
      rvCoprodLeftMap U (rvCoprodObject V W) u := by
  exact (congrArg (fun h : RVHom (rvCoprodObject U V) (rvCoprodObject U (rvCoprodObject V W)) =>
    h.map (rvCoprodLeftMap U V u))
      (rvCoprodInl_desc
        (rvCoprodDesc (rvCoprodInl U (rvCoprodObject V W))
          (rvCoprodInl V W ≫ rvCoprodInr U (rvCoprodObject V W)))
        (rvCoprodInr V W ≫ rvCoprodInr U (rvCoprodObject V W)))).trans
    (congrArg (fun h : RVHom U (rvCoprodObject U (rvCoprodObject V W)) => h.map u)
      (rvCoprodInl_desc (rvCoprodInl U (rvCoprodObject V W))
        (rvCoprodInl V W ≫ rvCoprodInr U (rvCoprodObject V W))))

theorem rvCoprodAssocExplicit_middle (U V W : RVObject (M := M) S k) (v : V.domain) :
    (rvCoprodAssocExplicit U V W).hom.map
      (rvCoprodLeftMap (rvCoprodObject U V) W (rvCoprodRightMap U V v)) =
      rvCoprodRightMap U (rvCoprodObject V W) (rvCoprodLeftMap V W v) := by
  exact (congrArg (fun h : RVHom (rvCoprodObject U V) (rvCoprodObject U (rvCoprodObject V W)) =>
    h.map (rvCoprodRightMap U V v))
      (rvCoprodInl_desc
        (rvCoprodDesc (rvCoprodInl U (rvCoprodObject V W))
          (rvCoprodInl V W ≫ rvCoprodInr U (rvCoprodObject V W)))
        (rvCoprodInr V W ≫ rvCoprodInr U (rvCoprodObject V W)))).trans
    (congrArg (fun h : RVHom V (rvCoprodObject U (rvCoprodObject V W)) => h.map v)
      (rvCoprodInr_desc (rvCoprodInl U (rvCoprodObject V W))
        (rvCoprodInl V W ≫ rvCoprodInr U (rvCoprodObject V W))))

theorem rvCoprodAssocExplicit_right (U V W : RVObject (M := M) S k) (w : W.domain) :
    (rvCoprodAssocExplicit U V W).hom.map (rvCoprodRightMap (rvCoprodObject U V) W w) =
      rvCoprodRightMap U (rvCoprodObject V W) (rvCoprodRightMap V W w) :=
  congrArg (fun h : RVHom W (rvCoprodObject U (rvCoprodObject V W)) => h.map w)
    (rvCoprodInr_desc _ _)

end IntegrationInACVF.Section7
