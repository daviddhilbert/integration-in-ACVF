import Integration7.GammaVolumeIndexedPresentations

/-! An indexed volume presentation with row density equal to an old
label retains exactly that label after its RV index prefix is appended. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem indexed_volume_presentation_density_label
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (P : F.IndexedPresentation BP) (δ : Fin a)
    (hDensity : ∀ s ∈ T, ∀ r w, F.rowDensity (rvValues s) r w ↔
      r ∈ F.object.rowDomain (rvValues s) ∧ w 0 = r δ)
    (u : P.finite.domain) :
    @VolumeForm.value M N hN _ P.finite.codes P.finite.domain P.form u = u.val (Fin.natAdd p δ) := by
  have hW := (P.density_iff u.val
    (@VolumeForm.map M N hN _ P.finite.codes P.finite.domain P.form u).val).mp ⟨u,rfl,rfl⟩
  have hs := (P.finite.domain_eq.le u.property).1
  exact ((hDensity (indexedLeft u.val) hs (indexedRight u.val) _).mp hW.2).2

theorem indexed_volume_presentation_density_nonzero
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (P : F.IndexedPresentation BP) (δ : Fin a)
    (hDensity : ∀ s ∈ T, ∀ r w, F.rowDensity (rvValues s) r w ↔
      r ∈ F.object.rowDomain (rvValues s) ∧ w 0 = r δ) :
    ∀ u : P.finite.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero := by
  intro u
  have hn := (@rv_nonzero_iff_raw M N hN
    (@VolumeForm.value M N hN _ P.finite.codes P.finite.domain P.form u)).mp
      (@VolumeForm.nonzero M N hN _ P.finite.codes P.finite.domain P.form u)
  rw [indexed_volume_presentation_density_label F BP P δ hDensity] at hn
  exact hn

end IntegrationInACVF.Section7
