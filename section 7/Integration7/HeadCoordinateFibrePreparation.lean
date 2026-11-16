module

public import Integration7.UnarySpecialRelativeConverse
public import IntegrationSection6.GammaHeadFibreParameters
public import IntegrationSection6.CanonicalContractionPrograms

@[expose] public section

/-! A genuine head preparation restricts to a genuine unary head
preparation after exactly its complementary VF tuple is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

def headCoordinateFibrePreparation (T : HeadPreparation U) (x : Fin n → VF (M := M)) :
    HeadPreparation (coordinateFibre U 0 (headFrozenTuple x)) where
  arity := T.arity
  target := coordinateFibre T.target 0 (headFrozenTuple x)
  map := coordinateFibreMap T.map 0 (specialRelative_unaryRelative T.special) (headFrozenTuple x)
  special := by
    obtain ⟨P,hP⟩ := T.special.choose_spec (headFrozenTuple x)
    have he : P.toMap = coordinateFibreMap T.map 0 (specialRelative_unaryRelative T.special) (headFrozenTuple x) :=
      @SpecialTransformations.DefinableGeometry.Map.ext LRV M (@CanonicalStructure.normalize M sM)
        _ _ (coordinateFibreBase S 0 (headFrozenTuple x))
        (coordinateFibre U 0 (headFrozenTuple x)) (coordinateFibre T.target 0 (headFrozenTuple x))
        P.toMap _ hP
    rw [← he]
    exact unary_special_relative P
  saturated := headSaturated_of_pullback ((headSaturated_iff_coordinateFibre T.target).mp T.saturated _)

theorem gamma_head_coordinate_fibre_preparation_map (T : HeadPreparation U)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (x : Fin n → VF (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (pointMapGraph (headCoordinateFibrePreparation T x).map) := by
  have h := gamma_coordinateFibreMap T.map hT 0 (specialRelative_unaryRelative T.special) (headFrozenTuple x)
  rw [coordinateGammaBase_head] at h
  exact h

theorem gamma_head_coordinate_fibre_preparation_target (T : HeadPreparation U)
    (hT : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (carrier (headCoordinateFibrePreparation T x).target) := gamma_head_fibre T.target hT x

end IntegrationInACVF.Section7
