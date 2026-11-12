import IntegrationSection6.GammaRVRealSets
import IntegrationSection6.LiftLoci
import Section4.MapCorestrict
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

theorem gamma_rv_graph_of_real_map
    {A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N a) (@Base.real M sM hM B)}
    {C : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N b) (@Base.real M sM hM B)}
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ (@Base.real M sM hM B) A C) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      ∃ u : A, u.val = p.2 ∧ (F u).val = q.2) := by
  let R := PresentedSet.univ (pointSpace (M := M) 0 a) (@Base.real M sM hM B)
  let pr := pointRVLabelsMap R
  let D : SpecialTransformations.Section5.DefSet (M := M) (@Base.real M sM hM B) 0 a := by
    letI : LRV.Structure M := N
    exact ⟨{p | ∃ x : R, x.val = p ∧ (pr x).val ∈
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (@Base.real M sM hM B) A},
      @SpecialTransformations.DefinableGeometry.Map.definable_preimage LRV M N _ _ (@Base.real M sM hM B) _ _ pr _
        (@SpecialTransformations.DefinableGeometry.DefSet.definable LRV M N _ (@Base.real M sM hM B) A)⟩
  let pD := @SpecialTransformations.DefinableGeometry.Map.restrict LRV M N _ _ (@Base.real M sM hM B) _ _ D pr (fun _ _ => Set.mem_univ _)
  have hpD (x : D) : (pD x).val ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (@Base.real M sM hM B) A) := by
    obtain ⟨y,hy,hA⟩ := x.property
    change y.val.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (@Base.real M sM hM B) A) at hA
    change x.val.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (@Base.real M sM hM B) A)
    exact (congrArg Prod.snd hy) ▸ hA
  let f := @SpecialTransformations.DefinableGeometry.Map.corestrict LRV M N _ _ (@Base.real M sM hM B) _ _ A pD hpD
  let g := @SpecialTransformations.DefinableGeometry.Map.comp LRV M N _ _ _ (@Base.real M sM hM B) _ _ _ (rvPointEmbeddingMap (@Base.real M sM hM B) b) (@SpecialTransformations.DefinableGeometry.Map.toUniv LRV M N _ _ (@Base.real M sM hM B) _ _ F)
  let H := @SpecialTransformations.DefinableGeometry.Map.comp LRV M N _ _ _ (@Base.real M sM hM B) _ _ _ g f
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph H)
  intro p q
  constructor
  · rintro ⟨x,hx,hq⟩
    exact ⟨⟨x.val.2,hpD x⟩,congrArg Prod.snd hx,congrArg Prod.snd hq⟩
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (@Base.real M sM hM B) A) := hu ▸ u.property
    let x : D := ⟨p,⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩⟩
    refine ⟨x,rfl,?_⟩
    apply Prod.ext (Subsingleton.elim _ _)
    change (F ⟨p.2,hp⟩).val = q.2
    exact (congrArg (fun v => (F v).val) (Subtype.ext hu.symm)).trans hq

end IntegrationInACVF.Section6
