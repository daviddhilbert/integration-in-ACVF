import IntegrationSection6.GammaRVRealization
import Section4.RVProductRestrictions
import Section5.GammaLift

/-! Real RV sets and products of Gamma RV sets retain their full original
Gamma definition. No field-generation hypothesis is involved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_rv_set_of_real
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) B.real) :
    GammaSetDefinable B {p : Point (M := M) 0 a |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real A} := by
  let F := @SpecialTransformations.DefinableGeometry.Map.restrict LRV M N _ _ B.real _ _ A
    (rvPointEmbeddingMap B.real a) (fun _ _ => Set.mem_univ _)
  let D := @SpecialTransformations.DefinableGeometry.Map.image LRV M N _ _ B.real _ _ F
  have h := (gammaLogicInput B).real_set (carrier D) (setDefinable D)
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p.2,hp⟩,Prod.ext (Subsingleton.elim _ _) rfl⟩
  · rintro ⟨x,hx⟩
    exact (show (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ B.real A) p.2 from (congrArg Prod.snd hx) ▸ x.property)

theorem gamma_rv_product_domain
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) S)
    (C : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N b) S)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A})
    (hC : GammaSetDefinable B {p : Point (M := M) 0 b |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C}) :
    GammaSetDefinable B {p : Point (M := M) 0 (a+b) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (@rvProductDomain M N S a b A C)} := by
  let L := gammaLogicInput B
  have hh := L.preimage_real (rvCoordinatePointMap (Fin.castAdd b) B.real) hA
  have ht := L.preimage_real (rvCoordinatePointMap (Fin.natAdd a) B.real) hC
  convert L.inter hh ht using 1
  ext p
  constructor
  · intro hp
    obtain ⟨u,hu,v,hv,hp⟩ := (@mem_rvProductDomain M N S a b A C p.2).mp hp
    have hleft : (fun j => p.2 (Fin.castAdd b j)) = u := by
      funext j
      exact (congrFun hp (Fin.castAdd b j)).symm.trans (Fin.append_left _ _ j)
    have hright : (fun j => p.2 (Fin.natAdd a j)) = v := by
      funext j
      exact (congrFun hp (Fin.natAdd a j)).symm.trans (Fin.append_right _ _ j)
    refine ⟨⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩,⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩⟩
    · exact (show (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) (fun j => p.2 (Fin.castAdd b j)) from hleft.symm ▸ hu)
    · exact (show (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C) (fun j => p.2 (Fin.natAdd a j)) from hright.symm ▸ hv)
  · rintro ⟨⟨x,hx,hu⟩,⟨y,hy,hv⟩⟩
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) (fun j => x.val.2 (Fin.castAdd b j)) at hu
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S C) (fun j => y.val.2 (Fin.natAdd a j)) at hv
    rw [hx] at hu
    rw [hy] at hv
    apply (@mem_rvProductDomain M N S a b A C p.2).mpr
    refine ⟨_,hu,_,hv,?_⟩
    funext j
    cases j using Fin.addCases <;> simp only [rvAppend,Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section6
