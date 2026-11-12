import IntegrationSection6.GammaAdmissibilitySchemata
import IntegrationSection6.GammaNativeFiniteBounds

/-! Uniform finite coordinate-slice bounds for an actual Gamma admissible
coordinate. Only the original real/Gamma names enter compactness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem GammaAdmissible.uniform_label_slices {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {U : GammaRVObject B k} {i : Fin k} (hAd : GammaAdmissible U i) :
    ∃ N : ℕ, ∀ t : Fin k → M, (∀ j, sortEval SortTag.rv (t j)) →
      {r | r ∈ gammaVolumeImage U ∧ ∀ j, j ≠ i → r j = t j}.Finite ∧
      {r | r ∈ gammaVolumeImage U ∧ ∀ j, j ≠ i → r j = t j}.ncard ≤ N := by
  let sr : Fin k → SortTag := fun _ => .rv
  let st := Fin.append sr sr
  let E : Set (Fin (k+k) → M) := {w | w ∈ sortedUniverse st ∧
    ∀ j, j ≠ i → w (Fin.natAdd k j) = w (Fin.castAdd k j)}
  have hE : DefinableOver B.real st E :=
    sorted_coordinates_except_eq_definable B.real st i (Fin.natAdd k) (Fin.castAdd k)
  have hImage := gammaVolumeImage_definable U
  let R : Set ((Fin k → M) × (Fin k → M)) :=
    {q | (∀ j, sortEval SortTag.rv (q.1 j)) ∧ q.2 ∈ gammaVolumeImage U ∧
      ∀ j, j ≠ i → q.2 j = q.1 j}
  have hR : DefinableOverBase B st {w | ((fun j => w (Fin.castAdd k j)),fun j => w (Fin.natAdd k j)) ∈ R} := by
    have h := hImage.inter_real_preimage st E hE (Fin.natAdd k)
    convert h using 1
    apply Set.ext
    intro w
    constructor
    · rintro ⟨ht,hr,he⟩
      refine ⟨hr,?_,he⟩
      have hrv := hImage.proper _ hr
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [st,sr,Fin.append_left] using ht l
      · simpa only [st,sr,Fin.append_right,Function.comp_apply] using hrv l
    · rintro ⟨hr,hs,he⟩
      refine ⟨?_,hr,he⟩
      intro j
      simpa only [st,sr,Fin.append_left] using hs (Fin.castAdd k j)
  let A : Set (Fin k → M) := sortedUniverse sr
  have hA : DefinableOverBase B sr A := real_definableOverBase B sr _ (sortedUniverse_definable B.real sr)
  have hfinite (t : Fin k → M) (ht : t ∈ A) : {r | (t,r) ∈ R}.Finite := by
    let tt : Fin k → CanonicalRV.RVSort M := fun j => ⟨t j,by simpa only [sr,sortEval,iRV] using ht j⟩
    have hf := (hAd.finite_label_slices hκ hs h00 hreal tt).image (fun r => fun j => (r j).val)
    apply hf.subset
    rintro r ⟨_,⟨u,hu⟩,hr⟩
    refine ⟨gammaVolumeValue U u,⟨⟨u,rfl⟩,?_⟩,hu⟩
    intro j hj
    apply Subtype.ext
    exact (congrFun hu j).trans (hr j hj)
  obtain ⟨N,hN⟩ := gamma_uniform_finite_tuple_rows hκ hs hreal hgamma sr sr A hA R hR hfinite
  refine ⟨N,?_⟩
  intro t ht
  have hb := hN t ht
  have he : {r | (t,r) ∈ R} = {r | r ∈ gammaVolumeImage U ∧ ∀ j, j ≠ i → r j = t j} := by
    apply Set.ext
    intro r
    exact ⟨fun h => h.2,fun h => ⟨ht,h⟩⟩
  rw [he] at hb
  exact hb

end IntegrationInACVF.Section6
