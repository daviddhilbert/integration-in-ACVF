import IntegrationSection6.GammaFiniteVolumePostcomposition
import IntegrationSection6.GammaWeightStrata
import Section4.RVFinitePadding
import IntegrationSection6.FiniteGammaIsoLaws

/-! Original-Gamma RV[k] data at a fixed internal real presentation.
The parameter set S describes codes only; every domain and volume graph
is still certified over the original Base B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPadAt (U : GammaObjectAt B S n) : GammaObjectAt B S (n+1) := by
  let P := gammaFiniteVolumePostcompose U.toGamma (@rvPadding M N hN n B.real)
    (@SpecialTransformations.DefinableGeometry.Map.finiteFibres_of_injective LRV M N _ _ B.real _ _ _
      (@rvPadding_injective M N hN n B.real)) (fun _ => Set.mem_univ _)
  exact {
    object := ⟨@rvPadObject M N hN S n U.object.obj,
      @rvPadObject_finite_volume M N hN S n U.object.obj U.object.property⟩,
    real_contains := U.real_contains
    domain_graph := U.domain_graph
    volume_graph := P.volume_graph }

def gammaCompressAt (U : GammaObjectAt B S (n+1))
    (hU : @rvLowWeightProperty M N S n U.object.obj) : GammaObjectAt B S n := by
  let P := gammaFiniteVolumePostcompose U.toGamma (@labelCompressionOver M N B.real n)
    (@labelCompressionOver_finite M N B.real n)
    (fun u => (@rvWeight_le_pred_iff_zero M N n (@RVObject.value M N S (n+1) U.object.obj u)).mp (hU u))
  exact {
    object := ⟨@rvCompressObject M N S n U.object.obj hU,P.finite_volume⟩,
    real_contains := U.real_contains
    domain_graph := U.domain_graph
    volume_graph := P.volume_graph }

def gammaWeightProjectionAt (U : GammaObjectAt B S (n+1)) : GammaObjectAt B S n :=
  gammaCompressAt (gammaLowRestrictionAt U) (@rvLowRestriction_weight M N S n U.object.obj)

end IntegrationInACVF.Section6.FiniteRV
