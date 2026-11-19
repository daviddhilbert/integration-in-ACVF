import Integration7.GammaNativeCommonNames
import Section9.SpecialJacobianGeneric

/-! A relation between mixed point spaces with a Gamma graph is a raw mixed
relation definable over any code set containing the common names of the
Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable pointSpace rawPointSpace rawPointMap
  PresentedSet RelationDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem point_relation_raw {S : Set M} {n m j r : ℕ}
    {R : Point (M := M) n m → Point (M := M) j r → Prop}
    (h : RelationDefinable (pointSpace n m) (pointSpace j r) S R) :
    RelationDefinable (rawPointSpace n m) (rawPointSpace j r) S R := by
  let P := pointSpace (M := M) n m
  let Q := pointSpace (M := M) j r
  let P' := rawPointSpace (M := M) n m
  let Q' := rawPointSpace (M := M) j r
  let g := rawPointMap (PresentedSet.univ P S)
  let f := rawPointMap (PresentedSet.univ Q S)
  have hg : (fun p p' => ∃ a : PresentedSet.univ P S, a.val = p ∧ (g a).val = p') =
      (fun p p' => p = p') := by
    funext p p'
    apply propext
    exact ⟨fun ⟨a, ha, he⟩ => ha.symm.trans he, fun he => ⟨⟨p, Set.mem_univ _⟩, rfl, he⟩⟩
  have hf : (fun q q' => ∃ a : PresentedSet.univ Q S, a.val = q ∧ (f a).val = q') =
      (fun q q' => q = q') := by
    funext q q'
    apply propext
    exact ⟨fun ⟨a, ha, he⟩ => ha.symm.trans he, fun he => ⟨⟨q, Set.mem_univ _⟩, rfl, he⟩⟩
  have hleft : RelationDefinable P' P S (fun x y => y = x) := by
    have hh := @Space.RelationDefinable.swap LRV M N P P' _ _
      (@SpecialTransformations.DefinableGeometry.Map.graph_definable LRV M N P P' S _ _ g)
    apply @Space.RelationDefinable.congr LRV M N P' P _ _ _ hh
    intro x y
    exact Iff.of_eq (congrFun (congrFun hg y) x)
  have hright : RelationDefinable Q Q' S (fun x y => x = y) := by
    apply @Space.RelationDefinable.congr LRV M N Q Q' _ _ _
      (@SpecialTransformations.DefinableGeometry.Map.graph_definable LRV M N Q Q' S _ _ f)
    intro x y
    exact Iff.of_eq (congrFun (congrFun hf x) y)
  have h₁ := @Space.RelationDefinable.comp LRV M N P' P Q _ _ _ hleft h
  have h₂ := @Space.RelationDefinable.comp LRV M N P' Q Q' _ _ _ h₁ hright
  apply @Space.RelationDefinable.congr LRV M N P' Q' _ _ _ h₂
  intro x y
  constructor
  · rintro ⟨_, ⟨_, rfl, h⟩, rfl⟩
    exact h
  · intro hr
    exact ⟨y, ⟨x, rfl, hr⟩, rfl⟩

theorem raw_mixed_relation_of_point (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    {n m j r : ℕ} {R : Point (M := M) n m → Point (M := M) j r → Prop}
    (h : RelationDefinable (pointSpace n m) (pointSpace j r) S R) :
    (rawMixedSpace (M := M) n m).RelationDefinable (rawMixedSpace (M := M) j r) S R := by
  have h' := point_relation_raw h
  let P := rawMixedSpace (M := M) n m
  let Q := rawMixedSpace (M := M) j r
  let H := P.relation Q R
  let HN := @Space.relation LRV M N (rawPointSpace (M := M) n m) (rawPointSpace (M := M) j r) R
  have he : H = HN := by
    ext z
    change (∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
      R (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩)) ↔
      (∃ hx : z ∘ Sum.inl ∈ P.domain, ∃ hy : z ∘ Sum.inr ∈ Q.domain,
        R (P.decode ⟨z ∘ Sum.inl, hx⟩) (Q.decode ⟨z ∘ Sum.inr, hy⟩))
    exact Iff.rfl
  have hd : @Set.Definable M S LRV N ((Fin n ⊕ Fin m) ⊕ (Fin j ⊕ Fin r)) H := by
    rw [he]
    exact h'
  change S.Definable LRV H
  exact Eq.mp (congrArg (fun T : LRV.Structure M =>
    @Set.Definable M S LRV T ((Fin n ⊕ Fin m) ⊕ (Fin j ⊕ Fin r)) H)
      (SpecialTransformations.Section8.normalize_eq_of_isCanonical hc)) hd

/-- A Gamma graph is a raw mixed relation over any code set containing the common names. -/
theorem gamma_raw_mixed_relation_common_names (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {S : Set M} (hNames : commonRealNames B ⊆ S) {n m j r : ℕ}
    {R : Point (M := M) n m → Point (M := M) j r → Prop} (h : GammaGraphDefinable B R) :
    (rawMixedSpace (M := M) n m).RelationDefinable (rawMixedSpace (M := M) j r) S R :=
  raw_mixed_relation_of_point hc
    (SpecialTransformations.Section5.RelationDefinable.mono _ _ (gamma_native_graph_common_names h) hNames)

end IntegrationInACVF.Section7
