import Integration7.GammaNamedZeroCoproducts
import Integration7.GammaNamedLiftClasses

/-! All-degree Gamma-named classes over `⟨C.base, Ξ⟩`, coded over the named code
context: RV classes (degree zero: Gamma zero objects up to Gamma isomorphism;
positive degree: Gamma blowup classes) and VF classes (Gamma isomorphism
classes). The lift is a bijection in every degree (Gamma-named Proposition
7.9), and the additive structure of RV classes (actual coproducts) is
transported to VF classes, making the integration map an additive
equivalence in every degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

/-- Gamma-named RV volume classes in every degree. -/
abbrev GammaNamedRVClasses : ℕ → Type
  | 0 => GammaZeroRVClasses (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M)
  | k+1 => GammaVolumeBlowupClasses hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) k

/-- Gamma-named VF volume classes in every degree. -/
abbrev GammaNamedVFClasses : ℕ → Type
  | 0 => GammaZeroVFClasses (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M)
  | k+1 => GammaVFVolumeClasses hc (gammaNamedCodeContext C Ξ hΞ) (gammaNamedBase C Ξ) k

instance gammaNamedRVClassesAddCommMonoid : (n : ℕ) → AddCommMonoid (GammaNamedRVClasses hc C Ξ hΞ n)
  | 0 => gammaZeroRVAddCommMonoid hc
  | _+1 => inferInstance

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

/-- The Gamma-named lift on classes in every degree. -/
def gammaNamedLiftOnClasses : (n : ℕ) → GammaNamedRVClasses hc C Ξ hΞ n → GammaNamedVFClasses hc C Ξ hΞ n
  | 0 => gammaZeroLiftOnClasses (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M)
  | _+1 => gammaNamedVolumeLiftOnClasses hc C Ξ hΞ hGenerated

include hγ hγ1 in
/-- **Gamma-named Proposition 7.9 (all degrees).** -/
theorem gamma_named_lift_on_classes_bijective (n : ℕ) :
    Function.Bijective (gammaNamedLiftOnClasses hc C Ξ hΞ hGenerated n) := by
  cases n with
  | zero =>
    exact gamma_zero_lift_on_classes_bijective hc (gammaNamedCodeContext C Ξ hΞ)
      (fun _ h => gamma_named_code_context_base C Ξ hΞ h) (gamma_named_code_context_names C Ξ hΞ) hGenerated
  | succ k => exact gamma_named_volume_lift_on_classes_bijective hc C Ξ hΞ hGenerated γ hγ hγ1

include hγ hγ1 in
/-- The Gamma-named integration map (inverse of the lift) in every degree. -/
def gammaNamedIntegrationEquiv (n : ℕ) : GammaNamedVFClasses hc C Ξ hΞ n ≃ GammaNamedRVClasses hc C Ξ hΞ n :=
  (Equiv.ofBijective _ (gamma_named_lift_on_classes_bijective hc C Ξ hΞ hGenerated γ hγ hγ1 n)).symm

include hγ hγ1 in
/-- The additive structure on Gamma-named VF classes, transported along integration. -/
def gammaNamedVFClassesAddCommMonoid (n : ℕ) : AddCommMonoid (GammaNamedVFClasses hc C Ξ hΞ n) :=
  (gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n).addCommMonoid

include hγ hγ1 in
/-- Integration as an additive equivalence in every degree. -/
def gammaNamedIntegrationAddEquiv (n : ℕ) :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1 n
    GammaNamedVFClasses hc C Ξ hΞ n ≃+ GammaNamedRVClasses hc C Ξ hΞ n :=
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1 n
  (gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n).addEquiv

end IntegrationInACVF.Section7.HK
