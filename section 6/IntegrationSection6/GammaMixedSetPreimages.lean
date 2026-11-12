import IntegrationSection6.GammaIsoRestrictions

/-! Definable inverse images and restricted isomorphisms in different
mixed arities. This permits a VF[k] dimensional presentation before
preparing membership predicates on the resulting k-coordinate lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a m b : ℕ}
variable {A : Set (Point (M := M) n a)} {C : Set (Point (M := M) m b)}

def gammaIsoSetPreimage (e : GammaIso B A C) (D : Set (Point (M := M) m b)) : Set (Point (M := M) n a) :=
  {p | ∃ x : A, x.val = p ∧ (e.equiv x).val ∈ D}

theorem gammaIsoSetPreimage_subset (e : GammaIso B A C) (D : Set (Point (M := M) m b)) :
    gammaIsoSetPreimage e D ⊆ A := by
  rintro p ⟨x,hx,_⟩
  exact hx ▸ x.property

theorem gammaIsoSetPreimage_definable (e : GammaIso B A C) (D : Set (Point (M := M) m b))
    (hD : GammaSetDefinable B D) : GammaSetDefinable B (gammaIsoSetPreimage e D) := by
  have h := (gammaLogicInput B).image_graph
    ((gammaLogicInput B).restrict_graph hD ((gammaLogicInput B).swap_graph e.graph))
  convert h using 1
  ext p
  constructor
  · rintro ⟨x,hx,hD⟩
    exact ⟨(e.equiv x).val,hD,x,hx,rfl⟩
  · rintro ⟨q,hq,x,hx,he⟩
    exact ⟨x,hx,he.symm ▸ hq⟩

theorem gammaIsoSetPreimage_mem (e : GammaIso B A C) (D : Set (Point (M := M) m b)) (x : A) :
    x.val ∈ gammaIsoSetPreimage e D ↔ (e.equiv x).val ∈ D := by
  constructor
  · rintro ⟨y,hy,hD⟩
    exact (Subtype.ext hy : y = x) ▸ hD
  · intro h
    exact ⟨x,rfl,h⟩

def gammaIsoSetPreimageIso (e : GammaIso B A C) (D : Set (Point (M := M) m b))
    (hDC : D ⊆ C) (hD : GammaSetDefinable B D) : GammaIso B (gammaIsoSetPreimage e D) D :=
  gammaIsoRestrict e (gammaIsoSetPreimage_subset e D) hDC
    (fun x => gammaIsoSetPreimage_mem e D x) (gammaIsoSetPreimage_definable e D hD)

end IntegrationInACVF.Section6
