import Integration7.FiniteVolumeCertificateCriterion
import Integration7.VolumeGammaWeightTuples

/-! The pointwise Gamma clause of a finite certificate is the explicit
first-order product-balance formula. The underlying chart remains fixed. -/

noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVVolumeIsoCertificate.toIso_of_balance {U V : PositiveRVVolumeObject (M := M) S k}
    {e : U.essential ≅ V.essential} (H : RVVolumeIsoCertificate U V e)
    (hΓ : ∀ u, Fin.append (rvValues (volumeGammaWeightTuple U u))
      (rvValues (volumeGammaWeightTuple V (finiteIsoMap e u))) ∈
        rvProductGammaBalance (M := M) ((k+1)+1)) : RVVolumeIso U V :=
  H.toIso (fun u => (volumeGammaWeightTuple_balance_iff U V u (finiteIsoMap e u)).mp (hΓ u))

theorem rvVolumeIso_finite_formula_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : U.essential ≅ V.essential) :
    (∃ f : RVVolumeIso U V, f.iso = e) ↔
      (∀ u, Fin.append (rvValues (volumeGammaWeightTuple U u))
        (rvValues (volumeGammaWeightTuple V (finiteIsoMap e u))) ∈
          rvProductGammaBalance (M := M) ((k+1)+1)) ∧ Nonempty (RVVolumeIsoCertificate U V e) := by
  rw [rvVolumeIso_finite_certificate_iff hc C e]
  exact and_congr_left (fun _ => forall_congr' (fun u =>
    (volumeGammaWeightTuple_balance_iff U V u (finiteIsoMap e u)).symm))

end IntegrationInACVF.Section7
