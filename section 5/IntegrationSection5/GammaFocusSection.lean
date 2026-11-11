import IntegrationSection5.FocusSection
import IntegrationSection5.GammaGraphOperations

/-! The focus section has its complete graph over the original Gamma base. -/

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
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m : ℕ}

def replacementGraphMap (j : Fin n) (S : Set M) :
    Map (PresentedSet.univ (spaceProd (pointSpace (M := M) n m)
      (SpecialTransformations.Section4.vfSpace 1)) S)
      (PresentedSet.univ (spaceProd (pointSpace n m) (pointSpace n m)) S) :=
  let H := PresentedSet.univ (spaceProd (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1)) S
  let fst := @SpecialTransformations.DefinableGeometry.Map.fst LRV M
    (CanonicalStructure.normalize (M := M)) (pointSpace n m)
    (SpecialTransformations.Section4.vfSpace 1) S H
  Map.comp (Map.inclusion (Set.subset_univ _)) (Map.pair fst (replaceCoordinateMap j H))

theorem replacementGraphMap_apply (j : Fin n) (S : Set M)
    (p : Point (M := M) n m) (x : VF (M := M)) :
    (replacementGraphMap j S ⟨(p,![x]),Set.mem_univ _⟩).val = (p,replace j p x) := rfl

theorem gamma_focusSection_graph {A : DefSet (M := M) S n m}
    {j : Fin n} {k : Fin m} (D : Focus A j k) (hA : IsRVPullback (carrier A))
    (hADef : GammaSetDefinable P (carrier A)) (hD : GammaFocusDefinable P D) :
    GammaGraphDefinable P (pointMapGraph (focusSectionMap D hA)) := by
  let L := gammaLogicInput P
  have hs : GammaScalarGraphDefinable P
      (fun p x => p ∈ carrier A ∩ D.locus ∧ x = D.center p) := hD.2
  have hactive := L.scalar_image_graph hs (replacementGraphMap j P.real)
  have hinactive := L.restrict_graph (L.sdiff hADef hD.1)
    (L.real_map_graph (Map.id (PresentedSet.univ (pointSpace n m) P.real)))
  apply GammaGraphDefinable.congr (L.union_graph hactive hinactive)
  intro p q
  constructor
  · rintro (⟨a,x,⟨ha,hx⟩,he⟩ | ⟨hp,a,ha,he⟩)
    · have hh := (replacementGraphMap_apply j P.real a x).symm.trans he
      have hp : a = p := congrArg Prod.fst hh
      subst p
      have hq := congrArg Prod.snd hh
      refine ⟨⟨a,ha.1⟩,rfl,?_⟩
      rw [focusSectionMap_active D hA _ ha.2]
      exact (congrArg (replace j a) hx).symm.trans hq
    · have heq : p = q := ha.symm.trans he
      refine ⟨⟨p,hp.1⟩,rfl,?_⟩
      rw [focusSectionMap_inactive D hA _ hp.2]
      exact heq
  · rintro ⟨a,rfl,he⟩
    by_cases hl : a.val ∈ D.locus
    · left
      refine ⟨a.val,D.center a.val,⟨⟨a.property,hl⟩,rfl⟩,?_⟩
      exact (replacementGraphMap_apply j P.real a.val (D.center a.val)).trans
        (Prod.ext rfl ((focusSectionMap_active D hA a hl).symm.trans he))
    · right
      refine ⟨⟨a.property,hl⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
      exact (congrArg Subtype.val (focusSectionMap_inactive D hA a hl)).symm.trans he

end IntegrationInACVF.Section5
