import IntegrationSection6.GammaRVGlobalRestriction
import Section5.GammaLiftRelation

/-! A full original-Gamma graph times an unchanged RV tuple retains its
full graph on a Gamma-definable source. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b r : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_rv_graph_append_id
    {P : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (a+r)) S}
    {Q : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N (b+r)) S}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S P Q)
    {R : Point (M := M) 0 a → Point (M := M) 0 b → Prop}
    (hR : GammaGraphDefinable B R)
    (hP : GammaSetDefinable B {p : Point (M := M) 0 (a+r) |
      p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S P})
    (hF : ∀ (p : Point (M := M) 0 (a+r)) (q : Point (M := M) 0 (b+r)),
      (∃ x : P, x.val = p.2 ∧ (F x).val = q.2) ↔
        (p.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S P ∧
          R (Fin.elim0,fun j => p.2 (Fin.castAdd r j)) (Fin.elim0,fun j => q.2 (Fin.castAdd r j)) ∧
          (fun j => p.2 (Fin.natAdd a j)) = (fun j => q.2 (Fin.natAdd b j)))) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (a+r)) (q : Point (M := M) 0 (b+r)) =>
      ∃ x : P, x.val = p.2 ∧ (F x).val = q.2) := by
  let L := gammaLogicInput B
  have hhead := hR.preimage_maps (rvCoordinatePointMap (Fin.castAdd r) B.real)
    (rvCoordinatePointMap (Fin.castAdd r) B.real)
  let Z := PresentedSet.univ (pointSpace (M := M) 0 r) B.real
  have ht := (L.real_map_graph (Map.id Z)).preimage_maps
    (rvCoordinatePointMap (Fin.natAdd a) B.real) (rvCoordinatePointMap (Fin.natAdd b) B.real)
  have htail : GammaGraphDefinable B (fun (p : Point (M := M) 0 (a+r)) (q : Point (M := M) 0 (b+r)) =>
      (fun j => p.2 (Fin.natAdd a j)) = (fun j => q.2 (Fin.natAdd b j))) := by
    apply GammaGraphDefinable.congr ht
    intro p q
    constructor
    · rintro ⟨z,hz,hq⟩
      exact congrArg Prod.snd (hz.symm.trans hq)
    · intro he
      exact ⟨⟨(Fin.elim0,fun j => p.2 (Fin.natAdd a j)),Set.mem_univ _⟩,rfl,
        Prod.ext rfl he⟩
  apply GammaGraphDefinable.congr (L.restrict_graph hP (hhead.inter htail))
  intro p q
  exact (hF p q).symm

end IntegrationInACVF.Section6
