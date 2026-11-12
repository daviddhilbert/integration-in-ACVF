import Section4.EmptyMaps
import Section5.GammaLift
import Section5.GammaInvariantLogic

/-! Restrict an actual Gamma isomorphism to compatible definable subsets,
without requiring a real presentation of the subsets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k l : ℕ}
variable {A A' : Set (Point (M := M) n m)} {D D' : Set (Point (M := M) k l)}

theorem gamma_mixed_empty_graph :
    GammaGraphDefinable B (fun (_ : Point (M := M) n m) (_ : Point (M := M) k l) => False) := by
  let Q := PresentedSet.univ (pointSpace (M := M) k l) B.real
  let F := @SpecialTransformations.DefinableGeometry.Map.emptyTo LRV M (@CanonicalStructure.normalize M sM)
    (@pointSpace M sM hM n m) (@pointSpace M sM hM k l) B.real Q
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph F)
  intro p q
  constructor
  · rintro ⟨x,_,_⟩
    exact x.property.elim
  · exact False.elim

def gammaEmptyMixedIso (hA : A = ∅) (hD : D = ∅) : GammaIso B A D := by
  letI : IsEmpty A := ⟨fun x => (hA.le x.property).elim⟩
  letI : IsEmpty D := ⟨fun x => (hD.le x.property).elim⟩
  refine ⟨Equiv.equivOfIsEmpty _ _,?_⟩
  apply GammaGraphDefinable.congr (gamma_mixed_empty_graph (B := B) (n := n) (m := m) (k := k) (l := l))
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨x,_,_⟩
    exact isEmptyElim x

end IntegrationInACVF.Section6
