import Integration7.FiniteVolumeIsoMaps
import Section4.RVCoproduct

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def rvCoprodIsoExplicit {U U' V V' : RVObject (M := M) S k} (e : U ≅ U') (f : V ≅ V') :
    rvCoprodObject U V ≅ rvCoprodObject U' V' where
  hom := rvCoprodDesc (e.hom ≫ rvCoprodInl U' V') (f.hom ≫ rvCoprodInr U' V')
  inv := rvCoprodDesc (e.inv ≫ rvCoprodInl U V) (f.inv ≫ rvCoprodInr U V)
  hom_inv_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, Category.assoc,
        rvCoprodInl_desc, ← Category.assoc, e.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, rvCoprodInr_desc, Category.assoc,
        rvCoprodInr_desc, ← Category.assoc, f.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply rvCoprod_hom_ext
    · rw [← Category.assoc, rvCoprodInl_desc, Category.assoc,
        rvCoprodInl_desc, ← Category.assoc, e.inv_hom_id, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, rvCoprodInr_desc, Category.assoc,
        rvCoprodInr_desc, ← Category.assoc, f.inv_hom_id, Category.id_comp, Category.comp_id]

theorem rvCoprodIsoExplicit_left {U U' V V' : RVObject (M := M) S k}
    (e : U ≅ U') (f : V ≅ V') (u : U.domain) :
    (rvCoprodIsoExplicit e f).hom.map (rvCoprodLeftMap U V u) =
      rvCoprodLeftMap U' V' (e.hom.map u) :=
  congrArg (fun h : RVHom U (rvCoprodObject U' V') => h.map u)
    (rvCoprodInl_desc (e.hom ≫ rvCoprodInl U' V') (f.hom ≫ rvCoprodInr U' V'))

theorem rvCoprodIsoExplicit_right {U U' V V' : RVObject (M := M) S k}
    (e : U ≅ U') (f : V ≅ V') (v : V.domain) :
    (rvCoprodIsoExplicit e f).hom.map (rvCoprodRightMap U V v) =
      rvCoprodRightMap U' V' (f.hom.map v) :=
  congrArg (fun h : RVHom V (rvCoprodObject U' V') => h.map v)
    (rvCoprodInr_desc (e.hom ≫ rvCoprodInl U' V') (f.hom ≫ rvCoprodInr U' V'))

end IntegrationInACVF.Section7
