import IntegrationSection6.FiniteGammaObjects
import IntegrationSection6.GammaRVGlobalRestriction
import Section5.GammaLiftRelation

/-! Combining a Gamma volume graph with globally definable label coordinates
retains the full graph of the packed RV key. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_volume_key_graph (U : GammaObjectAt B S n) {r : ℕ}
    (H : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (rvObjectArity U.object.obj)) B.real)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N r) B.real))
    (F : rvObjectDomain U.object.obj → (Fin (n+r) → CanonicalRV.RVSort M))
    (hF : ∀ u, F u = Fin.append (@RVObject.value M N S n U.object.obj u)
      (H ⟨u.val,Set.mem_univ _⟩).val) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj)) (q : Point (M := M) 0 (n+r)) =>
        ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧ F u = q.2) := by
  let L := gammaLogicInput B
  let P := PresentedSet.univ (pointSpace (M := M) 0 (rvObjectArity U.object.obj)) B.real
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N (n+r)) B.real
  let head := mapRVLabels 0 B.real (@selectRVTuple M N B.real (n+r) n (Fin.castAdd r) Q)
  let tail := mapRVLabels 0 B.real (@selectRVTuple M N B.real (n+r) r (Fin.natAdd n) Q)
  have hv := U.volume_graph.preimage_maps (Map.id P) head
  have hl := (L.real_map_graph (mapRVLabels 0 B.real H)).preimage_maps (Map.id P) tail
  apply GammaGraphDefinable.congr (hv.inter hl)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hv⟩,a,ha,hl⟩
    refine ⟨u,hu,?_⟩
    rw [hF]
    have ht : (H ⟨u.val,Set.mem_univ _⟩).val = fun j => q.2 (Fin.natAdd n j) := by
      have he := congrArg Prod.snd hl
      change (H ⟨a.val.2,Set.mem_univ _⟩).val = fun j => q.2 (Fin.natAdd n j) at he
      have hau : a.val.2 = u.val := (congrArg Prod.snd ha).trans hu.symm
      exact (congrArg (fun x => (H ⟨x,Set.mem_univ _⟩).val) hau).symm.trans he
    change (@RVObject.value M N S n U.object.obj u) = (fun j => q.2 (Fin.castAdd r j)) at hv
    funext j
    cases j using Fin.addCases with
    | left j => simpa only [Fin.append_left] using congrFun hv j
    | right j => simpa only [Fin.append_right] using congrFun ht j
  · rintro ⟨u,hu,hq⟩
    have hk := (hF u).symm.trans hq
    refine ⟨⟨u,hu,?_⟩,⟨p,Set.mem_univ _⟩,rfl,?_⟩
    · funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun hk (Fin.castAdd r j))
    · apply Prod.ext (Subsingleton.elim _ _)
      change (H ⟨p.2,Set.mem_univ _⟩).val = fun j => q.2 (Fin.natAdd n j)
      rw [← hu]
      funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun hk (Fin.natAdd n j))

end IntegrationInACVF.Section6.FiniteRV
