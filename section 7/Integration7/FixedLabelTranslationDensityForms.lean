module

public import Integration7.FixedLabelTranslationVolumes
public import Integration7.MixedRetainedLabelVolumeForms

@[expose] public section

/-! A selected fixed label supplies exactly the literal retained-coordinate
density used in contraction comparisons, on both sides of a translation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9 SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n d : ℕ}

theorem raw_fixed_rv_label_density_nonzero
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0) :
    ∀ p : rawSpecialSet hc (fixedRVLabelDomain A z hz), (p.val.2 (Fin.natAdd 0 j)).val ≠ iRVZero := by
  intro p
  have h := fixed_rv_label_domain_retained_value A z hz j η hj ⟨p.val,p.property⟩
  change (p.val.2 (Fin.natAdd 0 j)).val ≠ iRVZero
  rw [h]
  exact (rv_nonzero_iff_raw η).mp hη0

def fixedRVLabelDensityForm
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0) :
    VolumeForm (rawSpecialSet hc (fixedRVLabelDomain A z hz)) :=
  mixedRetainedLabelVolumeForm _ (Fin.natAdd 0 j) (raw_fixed_rv_label_density_nonzero hc A z hz j η hj hη0)

theorem fixed_rv_label_density_form_value
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S n 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    (p : rawSpecialSet hc (fixedRVLabelDomain A z hz)) :
    (fixedRVLabelDensityForm hc A z hz j η hj hη0).value p = η :=
  fixed_rv_label_domain_retained_value A z hz j η hj ⟨p.val,p.property⟩

theorem fixed_rv_label_translation_preserves_literal_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (A : DefSet (M := M) (C.base : Set M) n 0) (i : Fin n)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) (C.base : Set M)))
    (hC : ∀ p q : A, erase i p.val = erase i q.val → (c p).val 0 = (c q).val 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0) :
    PreservesVFVolume (fixedRVLabelDensityForm hc A z hz j η hj hη0)
      (fixedRVLabelDensityForm hc (relativeTranslationImage A i c) z hz j η hj hη0)
      (rawSpecialMap hc (fixedRVLabelMap (relativeTranslationToImage A i c) z hz)) := by
  apply fixed_rv_label_translation_preserves_volume hc C hn A i c hC z hz
  intro p
  rw [fixed_rv_label_density_form_value,fixed_rv_label_density_form_value]

end IntegrationInACVF.Section7
