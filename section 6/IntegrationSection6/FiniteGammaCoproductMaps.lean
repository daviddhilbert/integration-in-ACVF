import IntegrationSection6.FiniteGammaChartLaws
import IntegrationSection6.FiniteGammaCoproducts

/-! Maps and isomorphisms of finite coproducts, with original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U V U' V' : GammaObjectAt B S n}

@[simp] theorem isoAtMap_injective (e : GammaIsoAt U U') : Function.Injective (isoAtMap e.iso) :=
  (show Function.LeftInverse (isoAtMap e.iso.symm) (isoAtMap e.iso) from isoAtMap_inv_hom e.iso).injective

def coprodIsoMap (e : GammaIsoAt U U') (f : GammaIsoAt V V') :=
  let E := isoAtAmbient e.iso
  let F := isoAtAmbient f.iso
  let u := U'.object.obj
  let v := V'.object.obj
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  (rvCoprodDesc (E.hom ≫ rvCoprodInl u v)
    (F.hom ≫ rvCoprodInr u v)).map

@[simp] theorem coprodIsoMap_left (e : GammaIsoAt U U') (f : GammaIsoAt V V')
    (u : rvObjectDomain U.object.obj) :
    coprodIsoMap e f (@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u) =
      @rvCoprodLeftMap M N hN S n U'.object.obj V'.object.obj (isoAtMap e.iso u) := by
  let E := isoAtAmbient e.iso
  let F := isoAtAmbient f.iso
  let a := U.object.obj
  let b := U'.object.obj
  let c := V'.object.obj
  letI := N
  letI := hN
  exact congrArg (fun h : RVHom a (rvCoprodObject b c) => h.map u)
    (rvCoprodInl_desc (E.hom ≫ rvCoprodInl b c) (F.hom ≫ rvCoprodInr b c))

@[simp] theorem coprodIsoMap_right (e : GammaIsoAt U U') (f : GammaIsoAt V V')
    (v : rvObjectDomain V.object.obj) :
    coprodIsoMap e f (@rvCoprodRightMap M N hN S n U.object.obj V.object.obj v) =
      @rvCoprodRightMap M N hN S n U'.object.obj V'.object.obj (isoAtMap f.iso v) := by
  let E := isoAtAmbient e.iso
  let F := isoAtAmbient f.iso
  let a := V.object.obj
  let b := U'.object.obj
  let c := V'.object.obj
  letI := N
  letI := hN
  exact congrArg (fun h : RVHom a (rvCoprodObject b c) => h.map v)
    (rvCoprodInr_desc (E.hom ≫ rvCoprodInl b c) (F.hom ≫ rvCoprodInr b c))

theorem coprodIsoMap_inverse (e : GammaIsoAt U U') (f : GammaIsoAt V V')
    (a : rvObjectDomain (gammaCoprodAt U V).object.obj) :
    coprodIsoMap e.symm f.symm (coprodIsoMap e f a) = a := by
  rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · have ha : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
    rw [ha,coprodIsoMap_left,coprodIsoMap_left]
    change @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj (isoAtMap e.iso.symm (isoAtMap e.iso u)) = _
    rw [isoAtMap_inv_hom]
  · have ha : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
    rw [ha,coprodIsoMap_right,coprodIsoMap_right]
    change @rvCoprodRightMap M N hN S n U.object.obj V.object.obj (isoAtMap f.iso.symm (isoAtMap f.iso v)) = _
    rw [isoAtMap_inv_hom]

theorem coprodIsoMap_bijective (e : GammaIsoAt U U') (f : GammaIsoAt V V') :
    Function.Bijective (coprodIsoMap e f) := by
  refine ⟨(show Function.LeftInverse (coprodIsoMap e.symm f.symm) (coprodIsoMap e f) from coprodIsoMap_inverse e f).injective,?_⟩
  intro a
  exact ⟨coprodIsoMap e.symm f.symm a,coprodIsoMap_inverse e.symm f.symm a⟩

theorem coprodIsoMap_weight (e : GammaIsoAt U U') (f : GammaIsoAt V V')
    (a : rvObjectDomain (gammaCoprodAt U V).object.obj) :
    @rvWeight M N n (@RVObject.value M N S n (gammaCoprodAt U V).object.obj a) =
      @rvWeight M N n (@RVObject.value M N S n (gammaCoprodAt U' V').object.obj (coprodIsoMap e f a)) := by
  let E := isoAtAmbient e.iso
  let F := isoAtAmbient f.iso
  let u := U.object.obj
  let v := V.object.obj
  let u' := U'.object.obj
  let v' := V'.object.obj
  let C := (gammaCoprodAt U V).object.obj
  let C' := (gammaCoprodAt U' V').object.obj
  let forward := coprodIsoMap e f
  let backward := coprodIsoMap e.symm f.symm
  have hInv := coprodIsoMap_inverse e f a
  letI := N
  letI := hN
  have h := (rvCoprodDesc (E.hom ≫ rvCoprodInl u' v')
    (F.hom ≫ rvCoprodInr u' v')).volumetric a
  have h' := (rvCoprodDesc (E.inv ≫ rvCoprodInl u v)
    (F.inv ≫ rvCoprodInr u v)).volumetric (forward a)
  change rvWeight (C'.value (forward a)) ≤ rvWeight (C.value (backward (forward a))) at h'
  rw [hInv] at h'
  exact Nat.le_antisymm h h'

theorem gamma_coprodIsoMap_graph (e : GammaIsoAt U U') (f : GammaIsoAt V V') :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity (gammaCoprodAt U V).object.obj))
        (q : Point (M := M) 0 (rvObjectArity (gammaCoprodAt U' V').object.obj)) =>
        ∃ a : rvObjectDomain (gammaCoprodAt U V).object.obj,
          a.val = p.2 ∧ (coprodIsoMap e f a).val = q.2) := by
  let L := gammaLogicInput B
  have hl := L.comp_graph (L.swap_graph (gamma_leftTag_graph U (rvObjectArity V.object.obj)))
    (L.comp_graph e.graph (gamma_leftTag_graph U' (rvObjectArity V'.object.obj)))
  have hr := L.comp_graph (L.swap_graph (gamma_rightTag_graph V (rvObjectArity U.object.obj)))
    (L.comp_graph f.graph (gamma_rightTag_graph V' (rvObjectArity U'.object.obj)))
  apply GammaGraphDefinable.congr (L.union_graph hl hr)
  intro p q
  constructor
  · rintro (⟨z,⟨u,hu,hp⟩,w,⟨v,hv,hw⟩,⟨t,ht,hq⟩⟩ | ⟨z,⟨u,hu,hp⟩,w,⟨v,hv,hw⟩,⟨t,ht,hq⟩⟩)
    · have hvu : v = u := Subtype.ext (hv.trans hu.symm)
      have htv : t = isoAtMap e.iso v := Subtype.ext (ht.trans hw.symm)
      subst v; subst t
      refine ⟨@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u,hp,?_⟩
      rw [coprodIsoMap_left]
      exact hq
    · have hvu : v = u := Subtype.ext (hv.trans hu.symm)
      have htv : t = isoAtMap f.iso v := Subtype.ext (ht.trans hw.symm)
      subst v; subst t
      refine ⟨@rvCoprodRightMap M N hN S n U.object.obj V.object.obj u,hp,?_⟩
      rw [coprodIsoMap_right]
      exact hq
  · rintro ⟨a,ha,hq⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
      rw [he,coprodIsoMap_left] at hq
      exact Or.inl ⟨(Fin.elim0,u.val),⟨u,rfl,hu.trans ha⟩,
        (Fin.elim0,(isoAtMap e.iso u).val),⟨u,rfl,rfl⟩,⟨isoAtMap e.iso u,rfl,hq⟩⟩
    · have he : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
      rw [he,coprodIsoMap_right] at hq
      exact Or.inr ⟨(Fin.elim0,v.val),⟨v,rfl,hv.trans ha⟩,
        (Fin.elim0,(isoAtMap f.iso v).val),⟨v,rfl,rfl⟩,⟨isoAtMap f.iso v,rfl,hq⟩⟩

def gammaCoprodIsoAt (e : GammaIsoAt U U') (f : GammaIsoAt V V') :
    GammaIsoAt (gammaCoprodAt U V) (gammaCoprodAt U' V') where
  iso := @isoOfDefinableBijection M N S n (gammaCoprodAt U V).object (gammaCoprodAt U' V').object
    (coprodIsoMap e f) (coprodIsoMap_bijective e f) (coprodIsoMap_weight e f)
  graph := gamma_coprodIsoMap_graph e f

end IntegrationInACVF.Section6.FiniteRV
