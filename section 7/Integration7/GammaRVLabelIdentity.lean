import Integration7.GammaEssentialVolumeGraphs
import Section5.GammaInvariantLogic
import IntegrationSection6.GammaRVGlobalRestriction
import Section4.RVTagging

/-! Equality of proper RV label tuples is definable over every original
Gamma base, including the empty tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_rv_label_identity (B : Base (M := M)) (d : ℕ) :
    GammaGraphDefinable B (fun (p q : Point (M := M) 0 d) => p.2 = q.2) := by
  let P := PresentedSet.univ (pointSpace (M := M) 0 d) B.real
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph (Map.id P))
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    exact congrArg Prod.snd (ha.symm.trans hq)
  · intro h
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) h⟩

theorem gamma_rv_restricted_label_identity (B : Base (M := M)) {d : ℕ}
    (D : Set (Fin d → CanonicalRV.RVSort M))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 d | p.2 ∈ D}) :
    GammaGraphDefinable B (fun (p q : Point (M := M) 0 d) => p.2 ∈ D ∧ p.2 = q.2) :=
  (gammaLogicInput B).restrict_graph hD (gamma_rv_label_identity B d)

theorem gamma_rv_left_tag (B : Base (M := M)) (d e : ℕ) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 d) (q : Point (M := M) 0 (1+(d+e))) =>
      rvLeftTag (M := M) e p.2 = q.2) := by
  let Q := @DefSet.univ LRV M N (@rawRVSpace M N d) B.real
  let H := mapRVLabels 0 B.real (@rvLeftTagMap M N hN B.real d Q e)
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph H)
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    have he := congrArg Prod.snd hq
    change rvLeftTag (M := M) e a.val.2 = q.2 at he
    exact (congrArg (rvLeftTag (M := M) e) (congrArg Prod.snd ha)).symm.trans he
  · intro h
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) h⟩

theorem gamma_rv_right_tag (B : Base (M := M)) (d e : ℕ) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 e) (q : Point (M := M) 0 (1+(d+e))) =>
      rvRightTag (M := M) d p.2 = q.2) := by
  let Q := @DefSet.univ LRV M N (@rawRVSpace M N e) B.real
  let H := mapRVLabels 0 B.real (@rvRightTagMap M N hN B.real e Q d)
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph H)
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    have he := congrArg Prod.snd hq
    change rvRightTag (M := M) d a.val.2 = q.2 at he
    exact (congrArg (rvRightTag (M := M) d) (congrArg Prod.snd ha)).symm.trans he
  · intro h
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) h⟩

end IntegrationInACVF.Section7
