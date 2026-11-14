import Integration7.RVVolumeComposition
import Integration7.GammaVolumeCriterion

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volumeRatio_symm {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (v : V.essential.obj.domain) :
    volumeRatio V U e.symm v = (volumeRatio U V e (finiteIsoMap e.symm v))⁻¹ := by
  simp only [volumeRatio, finiteIsoMap_apply_symm, inv_div]

theorem volumeRatio_ne_zero {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (u : U.essential.obj.domain) : volumeRatio U V e u ≠ 0 :=
  div_ne_zero (U.essentialForm_nonzero u) (V.essentialForm_nonzero (finiteIsoMap e u))

def RVVolumeIso.symm (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) : RVVolumeIso V U where
  iso := f.iso.symm
  gamma v := by
    apply gammaVolumeEquation_of_absoluteRatio f.iso.symm v
    have h := congrArg Inv.inv (f.absolute_volumeRatio (finiteIsoMap f.iso.symm v))
    simpa only [volumeRatio_symm, map_inv₀, inv_div, finiteIsoMap_apply_symm] using h
  rv := by
    let e := f.iso.symm.trans f.iso
    let R := (volumeCorrespondence (finiteIsoMap e)).carrier
    have hmap (v : V.essential.obj.domain) : finiteIsoMap e v = v := by
      rw [finiteIsoMap_trans, finiteIsoMap_apply_symm]
    have hdiag : ∀ z ∈ R, ∀ i : Fin (k + 1),
        z (productLeft (k + 1) (k + 1) i) = z (productRight (k + 1) (k + 1) i) := by
      rintro z ⟨v, rfl⟩ i
      change productTuple (V.essential.obj.value v) (V.essential.obj.value (finiteIsoMap e v))
        (productLeft (k + 1) (k + 1) i) =
        productTuple (V.essential.obj.value v) (V.essential.obj.value (finiteIsoMap e v))
          (productRight (k + 1) (k + 1) i)
      rw [productTuple_left, productTuple_right, hmap]
    have hchain : RVAlmostEverywhere V.essential.obj.domain (k + 1) (fun v =>
        ∃ ω η : CanonicalRV.RVSort M,
          IsRVJacobianAt (volumeCorrespondence (finiteIsoMap f.iso.symm)).carrier
            (V.essential.obj.value v) (U.essential.obj.value (finiteIsoMap f.iso.symm v)) ω ∧
          IsRVJacobianAt (volumeCorrespondence (finiteIsoMap f.iso)).carrier
            (U.essential.obj.value (finiteIsoMap f.iso.symm v))
            (V.essential.obj.value (finiteIsoMap f.iso (finiteIsoMap f.iso.symm v))) η ∧
          IsRVJacobianAt R (V.essential.obj.value v)
            (V.essential.obj.value (finiteIsoMap f.iso (finiteIsoMap f.iso.symm v))) (η * ω)) := by
      obtain ⟨D, hD, hd, _, h⟩ := rvJacobian_chain_ae_finite_volume hc C (Nat.zero_lt_succ k)
        f.iso.symm f.iso V.essential_nonzero U.essential_nonzero V.essential_nonzero
      exact ⟨D, hD, hd, h⟩
    have hf := RVAlmostEverywhere.pullback_injective (finiteIsoMap f.iso.symm)
      (finiteIsoMap_injective f.iso.symm) f.rv
    apply RVAlmostEverywhere.mono (hchain.and hc C hf)
    rintro v ⟨⟨ω, η, hω, hη, hcomp⟩, hf⟩
    have hcomp' : IsRVJacobianAt R (V.essential.obj.value v) (V.essential.obj.value v) (η * ω) := by
      simpa only [finiteIsoMap_apply_symm] using hcomp
    have hp := rvJacobian_eq_one_of_diagonal R hdiag (V.essential.obj.value v) (η * ω) hcomp'
    rw [hη.unique hf] at hp
    have hw : ω = (volumeRatio U V f.iso (finiteIsoMap f.iso.symm v))⁻¹ := by
      apply mul_left_cancel₀ (volumeRatio_ne_zero f.iso (finiteIsoMap f.iso.symm v))
      exact hp.trans (mul_inv_cancel₀ (volumeRatio_ne_zero f.iso (finiteIsoMap f.iso.symm v))).symm
    rw [volumeRatio_symm, ← hw]
    exact hω

end IntegrationInACVF.Section7
