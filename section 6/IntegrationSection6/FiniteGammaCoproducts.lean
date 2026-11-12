import IntegrationSection6.FiniteGammaTagging

/-! Actual coproducts in RV[k] over the original Gamma base, using the
inherited tagged tuples. Domain and volume graphs keep the original names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_coprod_domain (U V : GammaObjectAt B S n) :
    GammaSetDefinable B
      {p : Point (M := M) 0 (1+(rvObjectArity U.object.obj+rvObjectArity V.object.obj)) |
        p.2 ∈ carrier (rvObjectDomain (@rvCoprodObject M N hN S n U.object.obj V.object.obj))} := by
  let L := gammaLogicInput B
  have h := L.union (L.image_graph (gamma_leftTag_graph U (rvObjectArity V.object.obj)))
    (L.image_graph (gamma_rightTag_graph V (rvObjectArity U.object.obj)))
  convert h using 1
  ext p
  constructor
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · exact Or.inl ⟨(Fin.elim0,u.val),u,rfl,hu⟩
    · exact Or.inr ⟨(Fin.elim0,v.val),v,rfl,hv⟩
  · rintro (⟨q,u,_,hu⟩ | ⟨q,v,_,hv⟩)
    · exact Or.inl ⟨u,hu⟩
    · exact Or.inr ⟨v,hv⟩

theorem gamma_coprod_volume (U V : GammaObjectAt B S n) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (1+(rvObjectArity U.object.obj+rvObjectArity V.object.obj)))
        (q : Point (M := M) 0 n) =>
        ∃ a : rvObjectDomain (@rvCoprodObject M N hN S n U.object.obj V.object.obj),
          a.val = p.2 ∧ (rvObjectVolume (@rvCoprodObject M N hN S n U.object.obj V.object.obj) a).val = q.2) := by
  let L := gammaLogicInput B
  have hl := L.comp_graph (L.swap_graph (gamma_leftTag_graph U (rvObjectArity V.object.obj))) U.volume_graph
  have hr := L.comp_graph (L.swap_graph (gamma_rightTag_graph V (rvObjectArity U.object.obj))) V.volume_graph
  apply GammaGraphDefinable.congr (L.union_graph hl hr)
  intro p q
  constructor
  · rintro (⟨z,⟨u,hu,htag⟩,⟨v,hv,hvol⟩⟩ | ⟨z,⟨u,hu,htag⟩,⟨v,hv,hvol⟩⟩)
    · have he : v = u := Subtype.ext (hv.trans hu.symm)
      subst v
      refine ⟨@rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u,htag,?_⟩
      exact (@rvCoprod_value_left M N hN S n U.object.obj V.object.obj u).trans hvol
    · have he : v = u := Subtype.ext (hv.trans hu.symm)
      subst v
      refine ⟨@rvCoprodRightMap M N hN S n U.object.obj V.object.obj u,htag,?_⟩
      exact (@rvCoprod_value_right M N hN S n U.object.obj V.object.obj u).trans hvol
  · rintro ⟨a,ha,hvol⟩
    rcases a.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · have he : a = @rvCoprodLeftMap M N hN S n U.object.obj V.object.obj u := Subtype.ext hu.symm
      have hU : (rvObjectVolume U.object.obj u).val = q.2 := by
        rw [he] at hvol
        exact (@rvCoprod_value_left M N hN S n U.object.obj V.object.obj u).symm.trans hvol
      exact Or.inl ⟨(Fin.elim0,u.val),⟨u,rfl,hu.trans ha⟩,u,rfl,hU⟩
    · have he : a = @rvCoprodRightMap M N hN S n U.object.obj V.object.obj v := Subtype.ext hv.symm
      have hV : (rvObjectVolume V.object.obj v).val = q.2 := by
        rw [he] at hvol
        exact (@rvCoprod_value_right M N hN S n U.object.obj V.object.obj v).symm.trans hvol
      exact Or.inr ⟨(Fin.elim0,v.val),⟨v,rfl,hv.trans ha⟩,v,rfl,hV⟩

def gammaCoprodAt (U V : GammaObjectAt B S n) : GammaObjectAt B S n where
  object := @rvFiniteCoprodObject M N hN S n U.object V.object
  real_contains := U.real_contains
  domain_graph := gamma_coprod_domain U V
  volume_graph := gamma_coprod_volume U V

end IntegrationInACVF.Section6.FiniteRV
