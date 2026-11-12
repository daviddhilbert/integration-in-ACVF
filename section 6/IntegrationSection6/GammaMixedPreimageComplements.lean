import IntegrationSection6.GammaMixedSetPreimages

/-! Complementary predicates pull back to complementary source pieces,
including isomorphisms between the actual restricted mixed sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a m b : ℕ}
variable {A : Set (Point (M := M) n a)} {C : Set (Point (M := M) m b)}

theorem gammaIsoSetPreimage_complement (e : GammaIso B A C) (D : Set (Point (M := M) m b)) :
    gammaIsoSetPreimage e (C \ D) = A \ gammaIsoSetPreimage e D := by
  ext p
  constructor
  · rintro ⟨x,hx,hC,hD⟩
    refine ⟨hx ▸ x.property,?_⟩
    intro hp
    exact hD ((gammaIsoSetPreimage_mem e D x).mp (hx.symm ▸ hp))
  · rintro ⟨hp,hn⟩
    let x : A := ⟨p,hp⟩
    exact ⟨x,rfl,(e.equiv x).property,fun h => hn ((gammaIsoSetPreimage_mem e D x).mpr h)⟩

def gammaIsoSetPreimageComplementIso (e : GammaIso B A C) (D : Set (Point (M := M) m b))
    (hD : GammaSetDefinable B D) : GammaIso B (A \ gammaIsoSetPreimage e D) (C \ D) :=
  (gammaIsoSetPreimageIso e (C \ D) (fun _ h => h.1)
    ((gammaLogicInput B).sdiff (e.target_definable (gammaLogicInput B)) hD)).congr
      (gammaIsoSetPreimage_complement e D) rfl

end IntegrationInACVF.Section6
