import IntegrationSection6.FiniteGammaIsoLaws

/-! Exact volume-tuple and density-label identities compose and invert
on the actual original-Gamma finite RV equivalences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6.FiniteRV

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n : ℕ} {U V W : GammaRVFiniteObject G n}

theorem gamma_iso_trans_coordinates
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (f : GammaRVIso V.toGammaRVObject W.toGammaRVObject)
    (he : ∀ u, gammaVolumeValue V.toGammaRVObject (e.equiv u) = gammaVolumeValue U.toGammaRVObject u)
    (hf : ∀ v, gammaVolumeValue W.toGammaRVObject (f.equiv v) = gammaVolumeValue V.toGammaRVObject v) :
    ∀ u, gammaVolumeValue W.toGammaRVObject ((gammaIsoTrans e f).equiv u) = gammaVolumeValue U.toGammaRVObject u :=
  fun u => (hf (e.equiv u)).trans (he u)

theorem gamma_iso_symm_coordinates
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (he : ∀ u, gammaVolumeValue V.toGammaRVObject (e.equiv u) = gammaVolumeValue U.toGammaRVObject u) :
    ∀ v, gammaVolumeValue U.toGammaRVObject ((gammaIsoSymm e).equiv v) = gammaVolumeValue V.toGammaRVObject v := by
  intro v
  have h := he (e.equiv.symm v)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem gamma_iso_trans_labels
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (f : GammaRVIso V.toGammaRVObject W.toGammaRVObject)
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object)) (η : Fin (rvObjectArity W.object))
    (he : ∀ u, (e.equiv u).val ε = u.val δ) (hf : ∀ v, (f.equiv v).val η = v.val ε) :
    ∀ u, ((gammaIsoTrans e f).equiv u).val η = u.val δ := fun u => (hf (e.equiv u)).trans (he u)

theorem gamma_iso_symm_labels
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (he : ∀ u, (e.equiv u).val ε = u.val δ) :
    ∀ v, ((gammaIsoSymm e).equiv v).val δ = v.val ε := by
  intro v
  have h := he (e.equiv.symm v)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end IntegrationInACVF.Section7
