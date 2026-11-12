import IntegrationSection6.GammaElementaryFocus

/-! A Gamma-definable literal lift recovers the complete Gamma domain
and volume graphs of its actual RV input, without adding parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rawLift_has_label (U : @RVObject M N S n) (u : rvObjectDomain U) :
    ∃ p : Point (M := M) n (rvObjectArity U), p ∈ carrier (rawLift U) ∧ p.2 = u.val := by
  obtain ⟨x,hx⟩ := @tupleRV_surjective M N hN n (@RVObject.value M N S n U u)
  exact ⟨(x,u.val),⟨u,rfl,hx.symm⟩,rfl⟩

theorem rv_domain_gamma_of_lift (U : @RVObject M N S n)
    (hL : GammaSetDefinable B (carrier (rawLift U))) :
    GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U) | p.2 ∈ carrier (rvObjectDomain U)} := by
  let L := gammaLogicInput B
  have hh := L.image_real (pointLabels B.real n (rvObjectArity U)) hL
  convert hh using 1
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp,hlabels⟩ := rawLift_has_label U ⟨q.2,hq⟩
    exact ⟨⟨p,Set.mem_univ _⟩,hp,Prod.ext (Subsingleton.elim _ _)
      ((pointLabels_snd B.real n (rvObjectArity U) _).trans hlabels)⟩
  · rintro ⟨p,hp,hq⟩
    obtain ⟨u,hu,_⟩ := hp
    have he := (pointLabels_snd B.real n (rvObjectArity U) p).symm.trans (congrArg Prod.snd hq)
    change q.2 ∈ carrier (rvObjectDomain U)
    exact (hu.trans he) ▸ u.property

end IntegrationInACVF.Section6
