import IntegrationSection6.GammaRVRestrictions
import Section4.RVCoordinates

/-! Full original-Gamma RV relations have real presentations after naming
only the finite representative tuple appearing in that relation. The full
Gamma graph remains the public certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def rvPointEmbeddingMap (R : Set M) (a : ℕ) :
    @SpecialTransformations.DefinableGeometry.Map LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) (@pointSpace M sM hM 0 a) R
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ R)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ R) := by
  refine @SpecialTransformations.DefinableGeometry.Map.ofCodes LRV M N
    (@SpecialTransformations.Section4.rawRVSpace M N a) (@pointSpace M sM hM 0 a) R
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ R)
    (fun x => (Fin.elim0,x)) (fun z => Sum.elim Fin.elim0 z) ?_ ?_ ?_
  · letI : LRV.Structure M := N
    intro i
    cases i with
    | inl i => exact i.elim0
    | inr i => exact Set.DefinableFun.proj LRV
  · intro c
    refine ⟨fun i => i.elim0,?_⟩
    intro i
    change @iRV M N (c.val i)
    exact (congrFun (@rvValues_decode M N a c) i) ▸ (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) c i).property
  · intro c
    apply Prod.ext (Subsingleton.elim _ _)
    funext i
    apply Subtype.ext
    exact (congrFun (@rvValues_decode M N a c) i).symm

theorem gamma_rv_relation_real_specialize
    {r : Point (M := M) 0 a → Point (M := M) 0 b → Prop} (h : GammaGraphDefinable B r) :
    ∃ d, ∃ t : Fin d → Code (M := M),
      @SpecialTransformations.DefinableGeometry.Space.RelationDefinable LRV M N
        (@SpecialTransformations.Section4.rawRVSpace M N a) (@SpecialTransformations.Section4.rawRVSpace M N b) (B.real ∪ Set.range (rawTuple t))
        (fun x y => r (Fin.elim0,x) (Fin.elim0,y)) := by
  obtain ⟨d,t,hr⟩ := h.real_specialize
  let R := B.real ∪ Set.range (rawTuple t)
  let P := @SpecialTransformations.Section4.rawRVSpace M N a
  let Q := @SpecialTransformations.Section4.rawRVSpace M N b
  let A := @pointSpace M sM hM 0 a
  let C := @pointSpace M sM hM 0 b
  let F := rvPointEmbeddingMap R a
  let G := rvPointEmbeddingMap R b
  have hf := @SpecialTransformations.DefinableGeometry.Map.graph_definable LRV M N P A R _ _ F
  have hg := @SpecialTransformations.DefinableGeometry.Map.graph_definable LRV M N Q C R _ _ G
  have hx := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.comp LRV M N P A C R _ _ hf hr
  have hy := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.swap LRV M N Q C R _ hg
  have hz := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.comp LRV M N P C Q R _ _ hx hy
  refine ⟨d,t,?_⟩
  apply @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.congr LRV M N P Q R _ _ hz
  intro x y
  constructor
  · rintro ⟨q,⟨p,⟨u,hu,hp⟩,hpq⟩,v,hv,hq⟩
    change (Fin.elim0,u.val) = p at hp
    change (Fin.elim0,v.val) = q at hq
    rw [← hp,← hq] at hpq
    simpa only [hu,hv] using hpq
  · intro hxy
    exact ⟨(Fin.elim0,y),⟨(Fin.elim0,x),⟨⟨x,Set.mem_univ _⟩,rfl,rfl⟩,hxy⟩,
      ⟨y,Set.mem_univ _⟩,rfl,rfl⟩

end IntegrationInACVF.Section6
