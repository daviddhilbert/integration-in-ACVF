import Integration7.GammaVolumeSchemaBounds
import IntegrationSection6.GammaSchemaFiniteRowPresentations
import IntegrationSection6.GammaWitnessUniformity

/-! Genuine finite rows over a definable parameter set admit one
uniform bound. Rebounding changes no coordinate or density formula. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem finiteSchema_valid_mono_bound (F : GammaFiniteRVSchema B p a k sp)
    {N L : ℕ} (hNL : N ≤ L) (z : Fin p → M) (h : (F.withBound N).valid z) :
    (F.withBound L).valid z := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro y hy
  exact ⟨(h.2.2.2 y hy).1,(h.2.2.2 y hy).2.trans hNL⟩

theorem finiteSchema_uniform_valid_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k sp) (A : Set (Fin p → M))
    (hA : DefinableOverBase B sp A) (hF : ∀ z ∈ A, F.finiteRow z) :
    ∃ N : ℕ, ∀ z ∈ A, (F.withBound N).valid z := by
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hreal hgamma sp A hA
    (fun N : ℕ => {z | (F.withBound N).valid z}) (fun N => (F.withBound N).valid_definable) (by
      intro z hz
      obtain ⟨P⟩ := F.realize_finiteRow z (hA.proper z hz) (hF z hz)
      exact F.exists_valid_bound hκ hs hreal hgamma z (hA.proper z hz) (hF z hz).2.1 P)
  refine ⟨J.sup id,?_⟩
  intro z hz
  obtain ⟨N,hN,hv⟩ := hJ z hz
  exact finiteSchema_valid_mono_bound F (Finset.le_sup (f := id) hN) z hv

theorem GammaRVVolumeSchema.uniform_valid_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k sp) (A : Set (Fin p → M))
    (hA : DefinableOverBase B sp A) (hF : ∀ z ∈ A, F.object.finiteRow z)
    (hDensity : ∀ z ∈ A, functionMapRowValid sp F.object.domain F.density z) :
    ∃ N : ℕ, ∀ z ∈ A, (F.withBound N).valid z := by
  obtain ⟨N,hN⟩ := finiteSchema_uniform_valid_bound hκ hs hreal hgamma F.object A hA hF
  exact ⟨N,fun z hz => ⟨hN z hz,hDensity z hz⟩⟩

end IntegrationInACVF.Section7
