import IntegrationSection6.NativeBalancedCorrespondenceLifts
import IntegrationSection6.NativeGammaLiftGraphs

/-! Every actual Gamma RV isomorphism lifts over its original generated
base, with no canonical-totalization hypothesis on the ambient model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaRVIso_native_volume_lift {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U V : GammaRVObject B k} (e : GammaRVIso U V) :
    ∃ A : Set (Fin (k + k) → M), @Set.Definable M B.real LRV N (Fin (k+k)) A ∧
      gammaRawVolumeCorrespondence U V e.equiv ⊆ rawLiftDomain A := by
  apply exists_native_balanced_correspondence_lift hκ hs h00 B hsmall hB
    Values.presentationValuation Values.presentation_compatible k _
    (gammaRawVolumeCorrespondence_definable U V e.equiv e.graph)
  · intro t s hz
    obtain ⟨u, hu⟩ := hz
    have ht : (fun i => (gammaVolumeValue U u i).val) = t := funext fun i => by
      simpa only [productTuple_left] using congrFun hu (productLeft k k i)
    have hv : (fun i => (gammaVolumeValue V (e.equiv u) i).val) = s := funext fun i => by
      simpa only [productTuple_right] using congrFun hu (productRight k k i)
    simpa only [ht, hv] using e.weight u
  · exact e.leftFinite
  · exact e.rightFinite

theorem gammaRVIso_liftIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) {U V : GammaRVObject B k} (e : GammaRVIso U V) :
    Nonempty (GammaIso B U.lift V.lift) := by
  obtain ⟨A,hA,hgood⟩ := gammaRVIso_native_volume_lift hκ hs h00 hreal hB e
  exact gammaLiftIso_of_graph e.equiv A hgood (nativeGammaLiftGraph_definable e A hA)

end IntegrationInACVF.Section6
