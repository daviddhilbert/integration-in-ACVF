module

public import Integration7.NativeRelativeTranslations
public import IntegrationSection5.GammaGraphOperations

@[expose] public section

/-! Actual relative translations and their images retain the original
Gamma base whenever the complete centre graph does. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

def relativeTranslationGraphMap (S : Set M) (i : Fin n) :
    Map (PresentedSet.univ (spaceProd (pointSpace (M := M) n a)
      (SpecialTransformations.Section4.vfSpace 1)) S)
      (PresentedSet.univ (spaceProd (pointSpace n a) (pointSpace n a)) S) :=
  let H := PresentedSet.univ (spaceProd (pointSpace n a) (SpecialTransformations.Section4.vfSpace 1)) S
  let fst := @SpecialTransformations.DefinableGeometry.Map.fst LRV M
    (CanonicalStructure.normalize (M := M)) (pointSpace n a)
    (SpecialTransformations.Section4.vfSpace 1) S H
  Map.comp (Map.inclusion (Set.subset_univ _)) (Map.pair fst (subtractMap i H))

theorem gamma_relative_translation_graph (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hΓ : GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z)) :
    GammaGraphDefinable B (pointMapGraph (relativeTranslationMap A i c)) := by
  have h := (gammaLogicInput B).scalar_image_graph hΓ (relativeTranslationGraphMap B.real i)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,x,⟨u,hu,hx⟩,he⟩
    have he' : (z,replace i z ((show VFType (M := M) from z.1 i)-x)) = (p,q) := he
    have hz := congrArg Prod.fst he'
    have hq := congrArg Prod.snd he'
    refine ⟨u,hu.trans hz,?_⟩
    rw [relative_translation_map_value,hx,hu]
    exact hq
  · rintro ⟨u,rfl,he⟩
    refine ⟨u.val,(c u).val 0,⟨u,rfl,rfl⟩,?_⟩
    exact Prod.ext rfl he

theorem gamma_relative_translation_image (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hΓ : GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z)) :
    GammaSetDefinable B (carrier (relativeTranslationImage A i c)) := by
  have h := (gammaLogicInput B).image_graph (gamma_relative_translation_graph A i c hΓ)
  convert h using 1
  apply Set.ext
  intro q
  constructor
  · rintro ⟨p,he⟩
    exact ⟨p.val,p,rfl,he⟩
  · rintro ⟨_,p,_,he⟩
    exact ⟨p,he⟩

theorem gamma_relative_translation_to_image_graph (A : DefSet (M := M) S n a) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hΓ : GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧ (c q).val 0 = z)) :
    GammaGraphDefinable B (pointMapGraph (relativeTranslationToImage A i c)) :=
  gamma_relative_translation_graph A i c hΓ

end IntegrationInACVF.Section7
