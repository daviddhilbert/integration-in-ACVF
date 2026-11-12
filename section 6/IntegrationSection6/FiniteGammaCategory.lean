import IntegrationSection6.FiniteGammaChartLaws

/-! The category of finite RV objects at a real presentation with every
object and morphism certified over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def homAtAmbient {U V : GammaObjectAt B S n} (f : U.object ⟶ V.object) :=
  (@finiteVolumeProperty M N S n).ι.map f

def homAtMap {U V : GammaObjectAt B S n} (f : U.object ⟶ V.object) :=
  @RVHom.map M N S n U.object.obj V.object.obj (homAtAmbient f)

structure GammaHomAt (U V : GammaObjectAt B S n) where
  hom : U.object ⟶ V.object
  graph : GammaGraphDefinable B
    (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
      (q : Point (M := M) 0 (rvObjectArity V.object.obj)) =>
      ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧ (homAtMap hom u).val = q.2)

theorem GammaHomAt.hom_ext {U V : GammaObjectAt B S n} {f g : GammaHomAt U V}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

def GammaHomAt.id (U : GammaObjectAt B S n) : GammaHomAt U U where
  hom := 𝟙 U.object
  graph := (GammaIsoAt.refl U).graph

def GammaHomAt.comp {U V W : GammaObjectAt B S n} (f : GammaHomAt U V) (g : GammaHomAt V W) : GammaHomAt U W where
  hom := f.hom ≫ g.hom
  graph := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph f.graph g.graph)
    intro p q
    constructor
    · rintro ⟨z,⟨u,hu,hz⟩,⟨v,hv,hq⟩⟩
      have he : v = homAtMap f.hom u := Subtype.ext (hv.trans hz.symm)
      exact ⟨u,hu,(congrArg (fun v => (homAtMap g.hom v).val) he).symm.trans hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨(Fin.elim0,(homAtMap f.hom u).val),⟨u,hu,rfl⟩,⟨homAtMap f.hom u,rfl,hq⟩⟩

instance gammaAtCategory : Category (GammaObjectAt B S n) where
  Hom := GammaHomAt
  id := GammaHomAt.id
  comp := GammaHomAt.comp
  id_comp f := GammaHomAt.hom_ext (Category.id_comp f.hom)
  comp_id f := GammaHomAt.hom_ext (Category.comp_id f.hom)
  assoc f g h := GammaHomAt.hom_ext (Category.assoc f.hom g.hom h.hom)

def gammaAtForget : GammaObjectAt B S n ⥤ @RVFiniteObject M N S n where
  obj U := U.object
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

def GammaIsoAt.toCategoryIso {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) : U ≅ V where
  hom := ⟨e.iso.hom,e.graph⟩
  inv := ⟨e.iso.inv,e.symm.graph⟩
  hom_inv_id := GammaHomAt.hom_ext e.iso.hom_inv_id
  inv_hom_id := GammaHomAt.hom_ext e.iso.inv_hom_id

def GammaIsoAt.ofCategoryIso {U V : GammaObjectAt B S n} (e : U ≅ V) : GammaIsoAt U V where
  iso := gammaAtForget.mapIso e
  graph := e.hom.graph

theorem gammaIsoAt_iff_iso (U V : GammaObjectAt B S n) : Nonempty (GammaIsoAt U V) ↔ Nonempty (U ≅ V) :=
  ⟨Nonempty.map GammaIsoAt.toCategoryIso,Nonempty.map GammaIsoAt.ofCategoryIso⟩

end IntegrationInACVF.Section6.FiniteRV
