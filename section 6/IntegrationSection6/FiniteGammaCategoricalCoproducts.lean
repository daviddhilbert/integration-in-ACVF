import IntegrationSection6.FiniteGammaCategory
import IntegrationSection6.FiniteGammaCoproducts

/-! Actual categorical coproducts with full original-Gamma morphism graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaCoprodInlAt (U V : GammaObjectAt B S n) : U ⟶ gammaCoprodAt U V where
  hom := ObjectProperty.homMk (@rvCoprodInl M N hN S n U.object.obj V.object.obj)
  graph := gamma_leftTag_graph U (rvObjectArity V.object.obj)

def gammaCoprodInrAt (U V : GammaObjectAt B S n) : V ⟶ gammaCoprodAt U V where
  hom := ObjectProperty.homMk (@rvCoprodInr M N hN S n U.object.obj V.object.obj)
  graph := gamma_rightTag_graph V (rvObjectArity U.object.obj)

def gammaCoprodDescHom {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) :=
  @rvCoprodDesc M N hN S n U.object.obj V.object.obj W.object.obj (homAtAmbient f.hom) (homAtAmbient g.hom)

def gammaCoprodDescMap {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) :=
  @RVHom.map M N S n (gammaCoprodAt U V).object.obj W.object.obj (gammaCoprodDescHom f g)

@[simp] theorem gammaCoprodDescMap_left {U V W : GammaObjectAt B S n}
    (f : U ⟶ W) (g : V ⟶ W) (u : rvObjectDomain U.object.obj) :
    gammaCoprodDescMap f g (@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u) = homAtMap f.hom u := by
  let A := U.object.obj
  let C := W.object.obj
  let F := homAtAmbient f.hom
  let G := homAtAmbient g.hom
  letI := N
  letI := hN
  exact congrArg (fun h : RVHom A C => h.map u) (rvCoprodInl_desc F G)

@[simp] theorem gammaCoprodDescMap_right {U V W : GammaObjectAt B S n}
    (f : U ⟶ W) (g : V ⟶ W) (v : rvObjectDomain V.object.obj) :
    gammaCoprodDescMap f g (@rvCoprodRightMap M N hN S n U.object.obj V.object.obj v) = homAtMap g.hom v := by
  let A := V.object.obj
  let C := W.object.obj
  let F := homAtAmbient f.hom
  let G := homAtAmbient g.hom
  letI := N
  letI := hN
  exact congrArg (fun h : RVHom A C => h.map v) (rvCoprodInr_desc F G)

theorem gamma_coprodDesc_graph {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity (gammaCoprodAt U V).object.obj))
        (q : Point (M := M) 0 (rvObjectArity W.object.obj)) =>
        ∃ a : rvObjectDomain (gammaCoprodAt U V).object.obj,
          a.val = p.2 ∧ (gammaCoprodDescMap f g a).val = q.2) := by
  let L := gammaLogicInput B
  have hl := L.comp_graph (L.swap_graph (gamma_leftTag_graph U (rvObjectArity V.object.obj))) f.graph
  have hr := L.comp_graph (L.swap_graph (gamma_rightTag_graph V (rvObjectArity U.object.obj))) g.graph
  apply GammaGraphDefinable.congr (L.union_graph hl hr)
  intro p q
  constructor
  · rintro (⟨z,⟨u,hu,hp⟩,⟨v,hv,hq⟩⟩ | ⟨z,⟨u,hu,hp⟩,⟨v,hv,hq⟩⟩)
    · have he : v = u := Subtype.ext (hv.trans hu.symm)
      subst v
      refine ⟨@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u,hp,?_⟩
      rw [gammaCoprodDescMap_left]
      exact hq
    · have he : v = u := Subtype.ext (hv.trans hu.symm)
      subst v
      refine ⟨@rvCoprodRightMap M N hN S n U.object.obj V.object.obj u,hp,?_⟩
      rw [gammaCoprodDescMap_right]
      exact hq
  · rintro ⟨a,ha,hq⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
      rw [he,gammaCoprodDescMap_left] at hq
      exact Or.inl ⟨(Fin.elim0,u.val),⟨u,rfl,hu.trans ha⟩,⟨u,rfl,hq⟩⟩
    · have he : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
      rw [he,gammaCoprodDescMap_right] at hq
      exact Or.inr ⟨(Fin.elim0,v.val),⟨v,rfl,hv.trans ha⟩,⟨v,rfl,hq⟩⟩

def gammaCoprodDescAt {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) : gammaCoprodAt U V ⟶ W where
  hom := ObjectProperty.homMk (gammaCoprodDescHom f g)
  graph := gamma_coprodDesc_graph f g

theorem gammaCoprodInl_desc {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) :
    gammaCoprodInlAt U V ≫ gammaCoprodDescAt f g = f := by
  apply GammaHomAt.hom_ext
  apply ObjectProperty.hom_ext
  exact @rvCoprodInl_desc M N hN S n U.object.obj V.object.obj W.object.obj (homAtAmbient f.hom) (homAtAmbient g.hom)

theorem gammaCoprodInr_desc {U V W : GammaObjectAt B S n} (f : U ⟶ W) (g : V ⟶ W) :
    gammaCoprodInrAt U V ≫ gammaCoprodDescAt f g = g := by
  apply GammaHomAt.hom_ext
  apply ObjectProperty.hom_ext
  exact @rvCoprodInr_desc M N hN S n U.object.obj V.object.obj W.object.obj (homAtAmbient f.hom) (homAtAmbient g.hom)

theorem gammaCoprod_hom_ext {U V W : GammaObjectAt B S n} {f g : gammaCoprodAt U V ⟶ W}
    (hl : gammaCoprodInlAt U V ≫ f = gammaCoprodInlAt U V ≫ g)
    (hr : gammaCoprodInrAt U V ≫ f = gammaCoprodInrAt U V ≫ g) : f = g := by
  apply GammaHomAt.hom_ext
  apply ObjectProperty.hom_ext
  apply @rvCoprod_hom_ext M N hN S n U.object.obj V.object.obj W.object.obj (homAtAmbient f.hom) (homAtAmbient g.hom)
  · exact congrArg (fun h : U ⟶ W => homAtAmbient h.hom) hl
  · exact congrArg (fun h : V ⟶ W => homAtAmbient h.hom) hr

def gammaCoprodIsColimit (U V : GammaObjectAt B S n) :
    IsColimit (BinaryCofan.mk (gammaCoprodInlAt U V) (gammaCoprodInrAt U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => gammaCoprodDescAt f g)
    gammaCoprodInl_desc gammaCoprodInr_desc (fun f g m hl hr =>
      gammaCoprod_hom_ext (hl.trans (gammaCoprodInl_desc f g).symm)
        (hr.trans (gammaCoprodInr_desc f g).symm))

instance gammaAtHasColimitPair (U V : GammaObjectAt B S n) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_,gammaCoprodIsColimit U V⟩

instance gammaAtHasBinaryCoproducts : HasBinaryCoproducts (GammaObjectAt B S n) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end IntegrationInACVF.Section6.FiniteRV
