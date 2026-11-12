import IntegrationSection6.GammaFamilyCoordinates
import IntegrationSection6.FiniteGammaCoproducts

/-! Uniform tagged coproduct formulas over the original Gamma base. The
actual native RV tags preserve the VF parameter tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def familyLeftTagMap (S : Set M) (p a b : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p a) S)
      (PresentedSet.univ (pointSpace (M := M) p (1+(a+b))) S) :=
  @mapRVLabels M sM hM p a (1+(a+b)) S
    (@rvLeftTagMap M N hN S a
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) S) b)

def familyRightTagMap (S : Set M) (p a b : ℕ) :
    Map (PresentedSet.univ (pointSpace (M := M) p b) S)
      (PresentedSet.univ (pointSpace (M := M) p (1+(a+b))) S) :=
  @mapRVLabels M sM hM p b (1+(a+b)) S
    (@rvRightTagMap M N hN S b
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N b) S) a)

theorem familyLeftTagMap_value (S : Set M) (p a b : ℕ)
    (x : PresentedSet.univ (pointSpace (M := M) p a) S) :
    (familyLeftTagMap S p a b x).val = (x.val.1,@rvLeftTag M N hN a b x.val.2) := rfl

theorem familyRightTagMap_value (S : Set M) (p a b : ℕ)
    (x : PresentedSet.univ (pointSpace (M := M) p b) S) :
    (familyRightTagMap S p a b x).val = (x.val.1,@rvRightTag M N hN b a x.val.2) := rfl

def GammaRVFamilyFormula.coprod (F : GammaRVFamilyFormula B p a k) (G : GammaRVFamilyFormula B p b k) :
    GammaRVFamilyFormula B p (1+(a+b)) k := by
  let L := gammaLogicInput B
  let lt := familyLeftTagMap B.real p a b
  let rt := familyRightTagMap B.real p a b
  let HL := fun (x : Point (M := M) p a) (w : Point (M := M) p (1+(a+b))) =>
    x ∈ F.domain ∧ (lt ⟨x,Set.mem_univ _⟩).val = w
  let HR := fun (x : Point (M := M) p b) (w : Point (M := M) p (1+(a+b))) =>
    x ∈ G.domain ∧ (rt ⟨x,Set.mem_univ _⟩).val = w
  have hL : GammaGraphDefinable B HL := L.restrict_graph F.domain_definable (gamma_global_map_graph lt)
  have hR : GammaGraphDefinable B HR := L.restrict_graph G.domain_definable (gamma_global_map_graph rt)
  let D : Set (Point (M := M) p (1+(a+b))) := {w | (∃ x, HL x w) ∨ ∃ x, HR x w}
  have hD : GammaSetDefinable B D := L.union (L.image_graph hL) (L.image_graph hR)
  let V := fun (w : Point (M := M) p (1+(a+b))) (q : Point (M := M) 0 k) =>
    (∃ x, HL x w ∧ F.volume x q) ∨ ∃ x, HR x w ∧ G.volume x q
  have hV : GammaGraphDefinable B V :=
    L.union_graph (L.comp_graph (L.swap_graph hL) F.volume_definable)
      (L.comp_graph (L.swap_graph hR) G.volume_definable)
  exact ⟨D,hD,V,hV⟩

end IntegrationInACVF.Section6
