import IntegrationSection6.GammaPreparedSelectedVolumes
import IntegrationSection6.GammaVolumeSliceLiftCarriers
import IntegrationSection6.GammaSwappedVolumes

/-! Exact lifted carriers of selected-volume slices of a prepared indexed
presentation. Both the base key and the original selected labels remain
literal coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaPreparedSelectedSlice_lift (C : DefSet (M := M) S p l)
    (BP : PreparedIndexPresentation B C) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hG : ∀ t ∈ preparedKeyDomain C, G.finiteRow (fun j => (t j).val))
    (hLabels : ∀ t ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (t j).val) r y ↔
      r ∈ G.rowDomain (fun j => (t j).val) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP) (t : Fin k → RV (M := M))
    (L : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ ((p+l)+a) p
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (fun j => (t j).val))) :
    L.toGamma.lift = {q : Point (M := M) p ((p+l)+a) |
      q.2 ∈ indexedDomain (preparedKeyDomain C) (fun s => G.rowDomain (fun j => (s j).val)) ∧
      indexedLeft q.2 ∘ Fin.castAdd l = @tupleRV M N hN p q.1 ∧ indexedRight q.2 ∘ ρ = t} := by
  apply (gammaVolumeSlicePresentation_lift (gammaSwapVolumeBlocks P.toGamma) t L).trans
  apply Set.ext
  intro q
  constructor
  · rintro ⟨u,hu,hv⟩
    rw [gammaSwapVolumeBlocks_value] at hv
    change (P.volume u).val ∘ (@finAddFlip k p) = Fin.append t (@tupleRV M N hN p q.1) at hv
    rw [prepared_selected_presentation_volume C BP G ρ hG hLabels P u,append_finAddFlip] at hv
    have hBase : indexedLeft u.val ∘ Fin.castAdd l = @tupleRV M N hN p q.1 := funext (fun j => by
      simpa only [Fin.append_right] using congrFun hv (Fin.natAdd k j))
    have hSel : indexedRight u.val ∘ ρ = t := funext (fun j => by
      simpa only [Fin.append_left] using congrFun hv (Fin.castAdd p j))
    have hDom := (Set.ext_iff.mp P.domain_eq u.val).mp u.property
    refine ⟨hu ▸ hDom,?_,?_⟩
    · exact (congrArg (fun v => indexedLeft v ∘ Fin.castAdd l) hu).symm.trans hBase
    · exact (congrArg (fun v => indexedRight v ∘ ρ) hu).symm.trans hSel
  · rintro ⟨hDom,hBase,hSel⟩
    let u := P.domainEquiv.symm ⟨q.2,hDom⟩
    refine ⟨u,rfl,?_⟩
    rw [gammaSwapVolumeBlocks_value]
    change (P.volume u).val ∘ (@finAddFlip k p) = Fin.append t (@tupleRV M N hN p q.1)
    rw [prepared_selected_presentation_volume C BP G ρ hG hLabels P u,append_finAddFlip]
    change Fin.append (indexedRight q.2 ∘ ρ) (indexedLeft q.2 ∘ Fin.castAdd l) = _
    exact congrArg₂ Fin.append hSel hBase

end IntegrationInACVF.Section6
