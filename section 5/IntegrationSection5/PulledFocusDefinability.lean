import IntegrationSection5.PulledFocusGeometry

/-! Original-real-base definability of the constructed source focus.
All graphs are complete graphs of actual maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {k : Fin l}

local notation "N" => (@CanonicalStructure.normalize M sM)

theorem sameRV_map_definable (T : Map A A) :
    SetDefinable (pointSpace 1 m) S
      {p | ∃ a : A, a.val = p ∧ SameRV (T a).val a.val} := by
  let K := keySpace (M := M) 1 m
  let g := Map.pair (Map.comp (keyMap A) T) (keyMap A)
  have hd : SetDefinable (spaceProd K K) S {p | p.1 = p.2} :=
    (@SpecialTransformations.DefinableGeometry.Space.definable_prod_iff LRV M N K K S Eq).mpr
      (@SpecialTransformations.DefinableGeometry.Space.relation_eq_definable LRV M N K S)
  have h := Map.definable_preimage g hd
  exact h

theorem pulledFocusLocus_definable (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) :
    SetDefinable (pointSpace 1 m) S (pulledFocusLocus f hf D hB) := by
  have h := SetDefinable.inter _ (Map.definable_preimage f D.locus_definable)
    (sameRV_map_definable (pulledFocusSection f hf D hB))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact ⟨⟨a, rfl, ha.1⟩, ⟨a, rfl, ha.2⟩⟩
  · rintro ⟨⟨a, rfl, ha⟩, ⟨b, hb, hrel⟩⟩
    have he : b = a := Subtype.ext hb
    exact ⟨a, rfl, ha, he ▸ hrel⟩

def unaryVFProjection (A : DefSet (M := M) S 1 m) :
    Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  @SpecialTransformations.DefinableGeometry.Map.fst LRV M (CanonicalStructure.normalize (M := M))
    (SpecialTransformations.Section4.vfSpace 1) (SpecialTransformations.Section4.rvSpace m) S A

theorem pulledFocusCentre_graph (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B)) :
    RelationDefinable (pointSpace 1 m) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier A ∩ pulledFocusLocus f hf D hB ∧
        z 0 = pulledFocusCentre f hf D hB p) := by
  let g := Map.comp (unaryVFProjection A) (pulledFocusSection f hf D hB)
  have hL := pulledFocusLocus_definable f hf D hB
  have hleft := @SpecialTransformations.DefinableGeometry.Space.Definable.left_relation LRV M N
    (pointSpace (M := M) 1 m) (SpecialTransformations.Section4.vfSpace 1) _ _ hL
  have h := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.inter LRV M N _ _ _ _ _
    hleft (Map.graph_definable g)
  apply RelationDefinable.congr _ _ h
  intro p z
  constructor
  · rintro ⟨hpL, a, rfl, hz⟩
    refine ⟨⟨a.property, hpL⟩, ?_⟩
    change (pulledFocusSection f hf D hB a).val.1 = z at hz
    exact (congrFun hz 0).symm.trans (pulledFocusCentre_apply f hf D hB a).symm
  · rintro ⟨⟨hpA, hpL⟩, he⟩
    let a : A := ⟨p, hpA⟩
    refine ⟨hpL, a, rfl, ?_⟩
    change (pulledFocusSection f hf D hB a).val.1 = z
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (pulledFocusCentre_apply f hf D hB a).symm.trans he.symm

/-- An actual source focus over the same real parameter base. The chosen
source cells and their centres are constructed from the target focus. -/
def pulledFocus (f : Map A B) (hf : Function.Bijective f) (hc : Contractible f)
    (D : Focus B 0 k) (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    {j : Fin m} (hTag : Tagged (carrier A) 0 j) : Focus A 0 j where
  toFocusGeometry := pulledFocusGeometry f hf hc D hA hB hTag
  locus_definable := pulledFocusLocus_definable f hf D hB
  center_graph := pulledFocusCentre_graph f hf D hB

end IntegrationInACVF.Section5
