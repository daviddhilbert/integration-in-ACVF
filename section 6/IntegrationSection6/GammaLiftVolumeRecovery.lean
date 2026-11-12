import IntegrationSection6.GammaLiftRecovery

/-! Recovering the full RV volume graph from a Gamma-definable literal
lift uses only projection, RV and relational composition over the real base. -/
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

theorem rv_volume_gamma_of_lift (U : @RVObject M N S n)
    (hL : GammaSetDefinable B (carrier (rawLift U))) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U)) (q : Point (M := M) 0 n) =>
        ∃ u : rvObjectDomain U, u.val = p.2 ∧ (rvObjectVolume U u).val = q.2) := by
  let L := gammaLogicInput B
  let f := pointLabels B.real n (rvObjectArity U)
  let g := pointVolumes B.real n (rvObjectArity U)
  have h := L.comp_graph (L.swap_graph (L.restrict_graph hL (L.real_map_graph f))) (L.real_map_graph g)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,⟨hz,a,ha,hl⟩,b,hb,hv⟩
    obtain ⟨u,hu,hvol⟩ := hz
    have hp : u.val = p.2 := hu.trans ((congrArg Prod.snd ha).symm.trans
      ((pointLabels_snd B.real n (rvObjectArity U) a).symm.trans (congrArg Prod.snd hl)))
    have hq : (rvObjectVolume U u).val = q.2 := by
      exact (hvol.trans (@normalized_tupleRV M sM hM n z.1)).trans
        ((congrArg (fun t : Point (M := M) n (rvObjectArity U) => fun j => rv (t.1 j)) hb).symm.trans
          ((pointVolumes_snd B.real n (rvObjectArity U) b).symm.trans (congrArg Prod.snd hv)))
    exact ⟨u,hp,hq⟩
  · rintro ⟨u,hu,hv⟩
    obtain ⟨x,hx⟩ := @tupleRV_surjective M N hN n (@RVObject.value M N S n U u)
    let z : Point (M := M) n (rvObjectArity U) := (x,u.val)
    have hz : z ∈ carrier (rawLift U) := ⟨u,rfl,hx.symm⟩
    have hlabel : (f ⟨z,Set.mem_univ _⟩).val = p :=
      Prod.ext (Subsingleton.elim _ _) ((pointLabels_snd B.real n (rvObjectArity U) _).trans hu)
    have hvol : (g ⟨z,Set.mem_univ _⟩).val = q := by
      apply Prod.ext (Subsingleton.elim _ _)
      exact (pointVolumes_snd B.real n (rvObjectArity U) _).trans
        (((@normalized_tupleRV M sM hM n x).symm.trans hx).trans hv)
    exact ⟨z,⟨hz,⟨z,Set.mem_univ _⟩,rfl,hlabel⟩,⟨z,Set.mem_univ _⟩,rfl,hvol⟩

def gammaRVObjectOfLift (hBS : B.real ⊆ S) (U : @RVObject M N S n)
    (hL : GammaSetDefinable B (carrier (rawLift U))) : GammaRVObject B n where
  codes := S
  real_contains := hBS
  object := U
  domain_graph := rv_domain_gamma_of_lift U hL
  volume_graph := rv_volume_gamma_of_lift U hL

@[simp] theorem gammaRVObjectOfLift_object (hBS : B.real ⊆ S) (U : @RVObject M N S n)
    (hL : GammaSetDefinable B (carrier (rawLift U))) :
    (gammaRVObjectOfLift hBS U hL).object = U := rfl

end IntegrationInACVF.Section6
