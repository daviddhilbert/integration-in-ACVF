import IntegrationSection6.GammaHeadFibreSliceMaps
import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection6.GammaIsoBaseEquality

/-! A frozen-tail permutation changes neither the head-fibre lift nor its
selected old RV labels. Only the order of already named VF parameters changes. -/
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
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

def gammaPermutedHeadFibreSliceLiftIso (T : HeadPreparation U)
    (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (ρ : Fin k → Fin a)
    (τ : Equiv.Perm (Fin n)) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B (vfPermutationImage T.contractedSet τ) (headVolumeIndex T ρ) x)
    (t : Fin k → RV (M := M))
    (Q : GammaFiniteGraphPresentation
      ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩ (1+T.arity) 1
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (fun j => (t j).val))) :
    GammaIso ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (carrier (coordinateFibre U 0 (headFrozenTuple (x ∘ τ.symm))) ∩ {q | q.2 ∘ ρ = t}) Q.toGamma.lift := by
  let f := gammaHeadFibreLiftIso T hT hTarget (x ∘ τ.symm)
  let f' := gammaIsoNamedRVLabels f ρ (headSelectedLabelIndex T ρ)
    (gammaHeadFibreLiftIso_labels T hT hTarget (x ∘ τ.symm) ρ) t
  rw [coordinateGammaBase_head] at f'
  have hb : (⟨(B.real ∪ Set.range (fun j => (x (τ.symm j)).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩ : Base (M := M)) =
      ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩ := by
    have h := vfPermutationParameterBase (B := B) τ x
    exact congrArg (fun C : Base (M := M) => (⟨C.real ∪ Set.range (fun j => (t j).val),C.gamma⟩ : Base (M := M))) h.symm
  apply (GammaIso.rebase f' hb).congr rfl
  ext q
  have hQ := Set.ext_iff.mp (selectedLabelFibrePresentation_slice_lift
    (vfPermutationImage T.contractedSet τ) (fun j : Fin 1 => Fin.castAdd T.arity j)
    (headSelectedLabelIndex T ρ) x P t Q) q
  have hh := headFibre_canonical_carrier T (x ∘ τ.symm) q
  change (_ ∧ _) ↔ _
  apply (and_congr hh Iff.rfl).trans
  constructor
  · rintro ⟨⟨hD,hr⟩,ht⟩
    apply hQ.mpr
    refine ⟨(vfPermutationImage_row T.contractedSet τ x q.2).mpr hD,ht,?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hr
  · intro h
    obtain ⟨hD,ht,hr⟩ := hQ.mp h
    exact ⟨⟨(vfPermutationImage_row T.contractedSet τ x q.2).mp hD,congrFun hr 0⟩,ht⟩

end IntegrationInACVF.Section6
