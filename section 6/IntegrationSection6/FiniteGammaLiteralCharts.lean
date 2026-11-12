import IntegrationSection6.FiniteGammaPresentationCharts
import IntegrationSection6.GammaLiftVolumeRecovery
import IntegrationSection6.GammaFocusLoci
import IntegrationSection6.NormalizedCanonicalLifts

/-! Gamma finite objects recovered from literal lifts and canonical labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaLiteralAt (hBS : B.real ⊆ S) (U : @RVFiniteObject M N S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.obj)}
    (h : @PresentsLift M N hN S n U.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) : GammaObjectAt B S n where
  object := U
  real_contains := hBS
  domain_graph := rv_domain_gamma_of_lift U.obj (by rw [normalizedPresentsLift_carrier h] at hA; exact hA)
  volume_graph := rv_volume_gamma_of_lift U.obj (by rw [normalizedPresentsLift_carrier h] at hA; exact hA)

def gammaCanonicalAt (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) : GammaObjectAt B S n :=
  gammaLiteralAt U.real_contains
    ⟨@canonicalRVKeyObject M N S n U.object.obj,
      (@finite_volume_iso M N hN S n U.object.obj _ (@canonicalRVKeyIso M N hN S n U.object.obj)).mp U.object.property⟩
    (normalizedPresentsLift_canonical h)
    (GammaPrimitiveDefinable.target (gammaLogicInput B) (.canonical A) hA)

def gammaCanonicalIsoAt (U : GammaObjectAt B S n)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN S n U.object.obj (normalizedPointSet A))
    (hA : GammaSetDefinable B (carrier A)) : GammaIsoAt (gammaCanonicalAt U h hA) U := by
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
    (@rawRVSpace M N (n+rvObjectArity U.object.obj)) B.real
  apply GammaIsoAt.ofAmbientFormula (@canonicalRVKeyIso M N hN S n U.object.obj).symm
    (@selectRVTuple M N B.real (n+rvObjectArity U.object.obj) (rvObjectArity U.object.obj) (Fin.natAdd n) Q)
  exact @canonicalRVKeyIso_inv_labels M N hN S n U.object.obj

end IntegrationInACVF.Section6.FiniteRV
