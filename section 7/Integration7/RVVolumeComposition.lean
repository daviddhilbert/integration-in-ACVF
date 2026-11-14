import Integration7.VolumeRelabeling
import Integration7.VolumeAlmostEverywhere
import Integration7.GammaVolumeCriterion
import Section9.GenericRVJacobianChain

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volumeRatio_trans {U V W : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (f : V.essential ≅ W.essential)
    (u : U.essential.obj.domain) :
    volumeRatio U W (e.trans f) u =
      volumeRatio V W f (finiteIsoMap e u) * volumeRatio U V e u := by
  change U.essentialForm.value u / W.essentialForm.value (finiteIsoMap f (finiteIsoMap e u)) =
    (V.essentialForm.value (finiteIsoMap e u) /
      W.essentialForm.value (finiteIsoMap f (finiteIsoMap e u))) *
        (U.essentialForm.value u / V.essentialForm.value (finiteIsoMap e u))
  rw [div_mul_div_comm,
    mul_comm (W.essentialForm.value (finiteIsoMap f (finiteIsoMap e u)))
      (V.essentialForm.value (finiteIsoMap e u)),
    mul_div_mul_left _ _ (V.essentialForm_nonzero (finiteIsoMap e u))]

def RVVolumeIso.trans (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (g : RVVolumeIso V W) : RVVolumeIso U W where
  iso := f.iso.trans g.iso
  gamma u := by
    apply gammaVolumeEquation_of_absoluteRatio (f.iso.trans g.iso) u
    change RVOperations.absoluteHom (volumeRatio U W (f.iso.trans g.iso) u) =
      (∏ i, RVOperations.absoluteHom
        (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u)) i)) /
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)
    have hv : (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap f.iso u) i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
        ((rv_nonzero_iff_raw _).mpr (V.essential_nonzero (finiteIsoMap f.iso u) i)))
    rw [volumeRatio_trans, map_mul, g.absolute_volumeRatio, f.absolute_volumeRatio,
      div_mul_div_comm,
      mul_comm (∏ i, RVOperations.absoluteHom
        (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u)) i))
        (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap f.iso u) i)),
      mul_div_mul_left _ _ hv]
  rv := by
    have hchain : RVAlmostEverywhere U.essential.obj.domain (k + 1) (fun u =>
        ∃ ω η : CanonicalRV.RVSort M,
          IsRVJacobianAt (volumeCorrespondence (finiteIsoMap f.iso)).carrier
            (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap f.iso u)) ω ∧
          IsRVJacobianAt (volumeCorrespondence (finiteIsoMap g.iso)).carrier
            (V.essential.obj.value (finiteIsoMap f.iso u))
            (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u))) η ∧
          IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (f.iso.trans g.iso))).carrier
            (U.essential.obj.value u)
            (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u))) (η * ω)) := by
      obtain ⟨D, hD, hd, _, h⟩ := rvJacobian_chain_ae_finite_volume hc C (Nat.zero_lt_succ k)
        f.iso g.iso U.essential_nonzero V.essential_nonzero W.essential_nonzero
      exact ⟨D, hD, hd, h⟩
    have hg := RVAlmostEverywhere.pullback_injective (finiteIsoMap f.iso)
      (finiteIsoMap_injective f.iso) g.rv
    apply RVAlmostEverywhere.mono ((f.rv.and hc C hg).and hc C hchain)
    rintro u ⟨⟨hf, hg⟩, ω, η, hω, hη, hfg⟩
    rw [hω.unique hf, hη.unique hg] at hfg
    change IsRVJacobianAt (volumeCorrespondence (finiteIsoMap (f.iso.trans g.iso))).carrier
      (U.essential.obj.value u)
      (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u)))
      (volumeRatio U W (f.iso.trans g.iso) u)
    rw [volumeRatio_trans]
    exact hfg

end IntegrationInACVF.Section7
