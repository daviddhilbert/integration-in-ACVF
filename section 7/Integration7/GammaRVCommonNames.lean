import Integration7.GammaNativeCommonNames
import IntegrationSection6.GammaRVRealization
import Integration7.VolumeSchemaUnderlyingIsomorphisms

/-! Fixed original-Gamma common names realize actual canonical raw RV
relation graphs over any containing real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

private theorem gamma_rv_relation_over_common_names
    {r : Point (M := M) 0 a → Point (M := M) 0 b → Prop} (h : GammaGraphDefinable B r) :
    @SpecialTransformations.DefinableGeometry.Space.RelationDefinable LRV M N
      (@rawRVSpace M N a) (@rawRVSpace M N b) (commonRealNames B)
      (fun x y => r (Fin.elim0,x) (Fin.elim0,y)) := by
  let R := commonRealNames B
  have hr := gamma_native_graph_common_names h
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

theorem gamma_raw_rv_relation_common_names
    (hc : CanonicalStructure.IsCanonical (M := M)) {R : Set M}
    (hNames : commonRealNames B ⊆ R)
    {r : Point (M := M) 0 a → Point (M := M) 0 b → Prop} (h : GammaGraphDefinable B r) :
    (SpecialTransformations.Section4.rawRVSpace (M := M) a).RelationDefinable (SpecialTransformations.Section4.rawRVSpace (M := M) b) R
      (fun x y => r (Fin.elim0,x) (Fin.elim0,y)) :=
  (canonicalRawRVRelation hc _ (gamma_rv_relation_over_common_names h)).mono _ _ hNames

end IntegrationInACVF.Section7
