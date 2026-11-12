import IntegrationSection6.GammaPreparedSelectedSliceCarriers
import IntegrationSection6.GammaPreparedFamilyKeyCharacterization
import IntegrationSection6.GammaPreparedFamilyLabelSlices

/-! The lift of every selected-volume slice of a prepared indexed object
is actually Gamma-isomorphic to the original mixed family with those old
RV labels fixed. -/
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
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)}

def gammaPreparedSelectedSliceLiftIso (C : DefSet (M := M) S p l)
    (e : GammaIso B A (carrier C)) (hA : GammaSetDefinable B A) (hC : IsRVPullback (carrier C))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (BP : PreparedIndexPresentation B C)
    (hG : ∀ s ∈ preparedKeyDomain C, G.finiteRow (fun j => (s j).val))
    (hLabels : ∀ s ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (s j).val) r y ↔
      r ∈ G.rowDomain (fun j => (s j).val) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP) (t : Fin k → RV (M := M))
    (L : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ ((p+l)+a) p
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks P.toGamma)).rowVolume (fun j => (t j).val))) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (vfSchemaSource A F ∩ {q | q.2 ∘ ρ = t}) L.toGamma.lift := by
  have hLift : L.toGamma.lift = preparedFamilyImage e F ∩
      {q | q.2 ∘ (fun j => Fin.natAdd (p+l) (ρ j)) = t} := by
    apply (gammaPreparedSelectedSlice_lift C BP G ρ hG hLabels P t L).trans
    apply Set.ext
    intro q
    have hNorm := @normalized_tupleRV M sM hM p q.1
    have hKey := preparedFamilyImage_key_iff C e hA hC F G hRows q
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hD,hV,hR⟩
      exact ⟨hKey.mpr ⟨hD,hV.trans hNorm⟩,hR⟩
    · rintro ⟨hD,hR⟩
      exact ⟨(hKey.mp hD).1,(hKey.mp hD).2.trans hNorm.symm,hR⟩
  exact (gammaPreparedFamilyNamedLabels e hA F ρ t).congr rfl hLift.symm

end IntegrationInACVF.Section6
