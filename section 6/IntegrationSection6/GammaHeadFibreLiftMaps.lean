import IntegrationSection6.GammaHeadFibreCoordinates
import IntegrationSection6.GammaRelativeRVFiniteness

/-! A head preparation gives an actual original-Gamma unary lift map after
freezing the other VF coordinates. Original RV labels remain a suffix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S (n+1) m}

def gammaHeadFibreLiftIso (T : HeadPreparation A)
    (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaIso (coordinateGammaBase B 0 (headFrozenTuple x))
      (carrier (coordinateFibre A 0 (headFrozenTuple x)))
      (carrier (canonicalImage (coordinateFibre T.target 0 (headFrozenTuple x)))) := by
  let Bt := coordinateGammaBase B 0 (headFrozenTuple x)
  let hi := specialRelative_unaryRelative T.special
  let f := coordinateFibreMap T.map 0 hi (headFrozenTuple x)
  let g := SpecialBijection.canonical (coordinateFibre T.target 0 (headFrozenTuple x))
  let e : GammaIso Bt (carrier (coordinateFibre A 0 (headFrozenTuple x)))
      (carrier (coordinateFibre T.target 0 (headFrozenTuple x))) :=
    ⟨Equiv.ofBijective f (coordinateFibreMap_bijective T.map T.bijective 0 hi _),
      gamma_coordinateFibreMap T.map hT 0 hi _⟩
  let d : GammaIso Bt (carrier (coordinateFibre T.target 0 (headFrozenTuple x)))
      (carrier (canonicalImage (coordinateFibre T.target 0 (headFrozenTuple x)))) :=
    ⟨g.equiv,GammaPrimitiveDefinable.graph (gammaLogicInput Bt) (.canonical _)
      (gamma_coordinateFibre T.target hTarget 0 _)⟩
  exact e.trans (gammaLogicInput Bt) d

def headSelectedLabelIndex (T : HeadPreparation A) {k : ℕ} (ρ : Fin k → Fin m) :
    Fin k → Fin (1+T.arity) := fun j => Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (ρ j))

theorem gammaHeadFibreLiftIso_labels (T : HeadPreparation A)
    (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
    {k : ℕ} (ρ : Fin k → Fin m) (a : coordinateFibre A 0 (headFrozenTuple x)) :
    ((gammaHeadFibreLiftIso T hT hTarget x).equiv a).val.2 ∘ headSelectedLabelIndex T ρ = a.val.2 ∘ ρ := by
  funext j
  let hi := specialRelative_unaryRelative T.special
  let f := coordinateFibreMap T.map 0 hi (headFrozenTuple x)
  let g := SpecialBijection.canonical (coordinateFibre T.target 0 (headFrozenTuple x))
  let i := suffixIndex (specialRelative_rvArity_le T.special) (ρ j)
  have hg := special_oldLabels g (f a) i
  have he : suffixIndex (special_chain_rvArity_le g.chain) i = Fin.natAdd 1 i := by
    apply Fin.ext
    simp only [suffixIndex,Fin.val_natAdd]
    omega
  rw [he] at hg
  exact hg.trans (specialRelative_oldLabels T.special
    ⟨coordinateInsert 0 (headFrozenTuple x) a.val,a.property⟩ (ρ j))

end IntegrationInACVF.Section6
