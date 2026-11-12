import IntegrationSection6.GammaSelectedLabelFibrePresentations
import IntegrationSection6.GammaSwappedVolumes
import IntegrationSection6.GammaVolumeSliceLiftCarriers

/-! Actual selected-volume fibre presentations have literal slice lifts.
Both blocks of selected old labels are retained, in the specified order. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a n k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem selectedLabelFibrePresentation_volume (U : DefSet (M := M) S p a)
    (ρ : Fin (n+k) → Fin a) (x : Fin p → VF (M := M))
    (P : SelectedLabelFibrePresentation B U ρ x) (u : P.domain) :
    gammaVolumeValue P.toGamma.toGammaRVObject u = u.val ∘ ρ :=
  ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm

theorem selectedLabelFibrePresentation_slice_lift (U : DefSet (M := M) S p a)
    (ρ : Fin n → Fin a) (τ : Fin k → Fin a) (x : Fin p → VF (M := M))
    (P : SelectedLabelFibrePresentation B U (Fin.append ρ τ) x) (t : Fin k → RV (M := M))
    (Q : GammaFiniteGraphPresentation
      ⟨(B.real ∪ Set.range (fun j => (x j).val)) ∪ Set.range (fun j => (t j).val),B.gamma⟩ a n
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (fun j => (t j).val))) :
    Q.toGamma.lift = {q : Point (M := M) n a |
      (x,q.2) ∈ carrier U ∧ q.2 ∘ τ = t ∧ q.2 ∘ ρ = (fun j => rv (q.1 j))} := by
  apply (gammaVolumeSlicePresentation_lift (gammaSwapVolumeBlocks P.toGamma) t Q).trans
  ext q
  have hvol (u : P.domain) :
      gammaVolumeValue (gammaSwapVolumeBlocks P.toGamma).toGammaRVObject u =
        Fin.append (u.val ∘ τ) (u.val ∘ ρ) := by
    rw [gammaSwapVolumeBlocks_value,selectedLabelFibrePresentation_volume]
    change (u.val ∘ Fin.append ρ τ) ∘ finAddFlip = _
    funext j
    cases j using Fin.addCases <;> simp only [Function.comp_apply,
      finAddFlip_apply_castAdd,finAddFlip_apply_natAdd,Fin.append_left,Fin.append_right]
  constructor
  · rintro ⟨u,hu,hv⟩
    have hD : (x,q.2) ∈ carrier U := by
      have hd := (Set.ext_iff.mp P.domain_eq u.val).mp u.property
      exact hu ▸ hd
    rw [hvol] at hv
    refine ⟨hD,?_,?_⟩
    · funext j
      have he : u.val (τ j) = t j := by
        simpa only [Fin.append_left,Function.comp_apply] using congrFun hv (Fin.castAdd n j)
      exact (congrArg (fun r => r (τ j)) hu).symm.trans he
    · have hNrv := @normalized_tupleRV M sM hM n q.1
      funext j
      have he : u.val (ρ j) = @tupleRV M N hN n q.1 j := by
        simpa only [Fin.append_right,Function.comp_apply] using congrFun hv (Fin.natAdd k j)
      exact (congrArg (fun r => r (ρ j)) hu).symm.trans (he.trans (congrFun hNrv j))
  · rintro ⟨hD,ht,hr⟩
    let u : P.domain := ⟨q.2,(Set.ext_iff.mp P.domain_eq q.2).mpr hD⟩
    refine ⟨u,rfl,?_⟩
    rw [hvol]
    exact congrArg₂ Fin.append ht (hr.trans (@normalized_tupleRV M sM hM n q.1).symm)

end IntegrationInACVF.Section6
