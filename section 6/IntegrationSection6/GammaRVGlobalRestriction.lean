import IntegrationSection6.GammaGlobalRestriction

/-! Original-Gamma graphs of explicit maps between RV domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {d e : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_rv_graph_of_global_formula
    {P : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N d) S}
    {Q : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N e) S}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S P Q)
    (G : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ B.real
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N d) B.real)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N e) B.real))
    (hP : GammaSetDefinable B {p : Point (M := M) 0 d | p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S P})
    (hF : ∀ a : P, (F a).val = (G ⟨a.val,Set.mem_univ _⟩).val) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 d) (q : Point (M := M) 0 e) =>
      ∃ a : P, a.val = p.2 ∧ (F a).val = q.2) := by
  let H := mapRVLabels 0 B.real G
  let L := gammaLogicInput B
  apply GammaGraphDefinable.congr (L.restrict_graph hP (L.real_map_graph H))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    refine ⟨⟨p.2,hp⟩,rfl,?_⟩
    have he : (G ⟨p.2,Set.mem_univ _⟩).val = q.2 := by
      have ht := congrArg Prod.snd hq
      change (G ⟨a.val.2,Set.mem_univ _⟩).val = q.2 at ht
      exact (congrArg (fun b => (G b).val) (Subtype.ext (congrArg Prod.snd ha).symm)).trans ht
    exact (hF ⟨p.2,hp⟩).trans he
  · rintro ⟨a,ha,hq⟩
    refine ⟨(show p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S P from ha ▸ a.property),⟨p,Set.mem_univ _⟩,rfl,?_⟩
    apply Prod.ext (Subsingleton.elim _ _)
    change (G ⟨p.2,Set.mem_univ _⟩).val = q.2
    exact ((congrArg (fun b => (G b).val) (Subtype.ext ha.symm)).trans (hF a).symm).trans hq

end IntegrationInACVF.Section6
