import IntegrationSection6.GammaHeadSelectedFiniteness
import IntegrationSection6.GammaSelectedFibreSliceCarriers
import IntegrationSection6.GammaNamedIsoRestrictions
import IntegrationSection6.FiniteGammaLiftGluing

/-! Selected-volume slices of a head-contracted RV fibre have actual
unary lifts isomorphic to the original coordinate fibre with the selected
old labels fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m k : ℕ}
variable {A : DefSet (M := M) S (n+1) m}

def gammaHeadFibreSliceLiftIso (T : HeadPreparation A)
    (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin m)
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T ρ) x)
    (t : Fin k → RV (M := M))
    (Q : GammaFiniteGraphPresentation
      ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩ (1+T.arity) 1
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (fun j => (t j).val))) :
    GammaIso ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (carrier (coordinateFibre A 0 (headFrozenTuple x)) ∩ {q | q.2 ∘ ρ = t}) Q.toGamma.lift := by
  let f := gammaHeadFibreLiftIso T hT hTarget x
  let f' := gammaIsoNamedRVLabels f ρ (headSelectedLabelIndex T ρ)
    (gammaHeadFibreLiftIso_labels T hT hTarget x ρ) t
  rw [coordinateGammaBase_head] at f'
  apply f'.congr rfl
  apply Set.ext
  intro q
  have hQ := Set.ext_iff.mp
    (selectedLabelFibrePresentation_slice_lift T.contractedSet
      (fun j : Fin 1 => Fin.castAdd T.arity j) (headSelectedLabelIndex T ρ) x P t Q) q
  have hh := headFibre_canonical_carrier T x q
  change (_ ∧ _) ↔ _
  apply (and_congr hh Iff.rfl).trans
  constructor
  · rintro ⟨⟨hD,hr⟩,ht⟩
    apply hQ.mpr
    refine ⟨hD,ht,?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hr
  · intro h
    obtain ⟨hD,ht,hr⟩ := hQ.mp h
    exact ⟨⟨hD,congrFun hr 0⟩,ht⟩

end IntegrationInACVF.Section6
