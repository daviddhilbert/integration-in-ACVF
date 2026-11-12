import IntegrationSection6.FiniteLiftFibres
import IntegrationSection5.StandardContractionGammaNormalization
import Section5.GammaFiniteFibres

/-! Standard contractions of finite RV-fibre sets are actual objects of
RV[k], with their original-Gamma domain, volume and natural lift graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaFiniteContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVFiniteObject B n where
  toGammaRVObject := C.gammaNormalizedObject hBS (gamma_program_final_set C.program hC)
  finite_volume := by
    let e := C.gammaNormalizedLiftIso hBS hA hC
    apply finite_volume_of_finite_lift_fibres C.normalizedObject
    exact finiteRVFibres_of_gammaIso hκ hs B hsmall e
      (fun p _ => @vfTupleTrdeg_le_arity M N hN B.real n p.1) hfin

@[simp] theorem gammaFiniteContraction_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    {σ : Equiv.Perm (Fin n)} (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    (gammaFiniteContraction hκ hs hsmall hBS hA hfin C hC).object = C.normalizedObject := rfl

end IntegrationInACVF.Section6.FiniteRV
