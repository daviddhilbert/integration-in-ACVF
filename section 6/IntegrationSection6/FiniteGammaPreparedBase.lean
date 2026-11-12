import IntegrationSection6.GammaPreparedDescent
import IntegrationSection6.FiniteLiftFibres
import Section5.GammaFiniteFibres

/-! Preparing a pure VF base produces an actual object of RV[n]. The RV
key tuple is finite over its n volume labels, even though the key set may
be infinite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPreparedBase {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n 0}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hC : IsRVPullback (carrier C)) : GammaRVFiniteObject B n := by
  let hCΓ := GammaChainDefinable.target B T.chain hT
  let U := gammaPullbackObject (gammaLogicInput B) hBS C hCΓ
  let eT : GammaIso B (carrier A) (carrier C) :=
    ⟨T.equiv,GammaChainDefinable.graph (gammaLogicInput B) T.chain hT⟩
  let e := eT.trans (gammaLogicInput B) (gamma_pullback_iso (gammaLogicInput B) hBS C hCΓ hC)
  refine ⟨U,?_⟩
  apply finite_volume_of_finite_lift_fibres U.object
  exact finiteRVFibres_of_gammaIso hκ hs B hsmall e
    (fun p _ => @vfTupleTrdeg_le_arity M N hN B.real n p.1)
    (fun _ => Set.toFinite _)

theorem gammaPreparedBase_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n 0}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hC : IsRVPullback (carrier C)) :
    (gammaPreparedBase hκ hs hsmall hBS T hT hC).object = pullbackObject C := rfl

end IntegrationInACVF.Section6.FiniteRV
