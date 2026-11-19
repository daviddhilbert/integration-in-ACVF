import Integration7.GammaNamedRVSemiring
import Integration7.HKGradedClassIntegration

/-! **Gamma-named Theorem 7.10.** The graded semiring of Gamma-named RV
classes over `⟨C.base, Ξ⟩` (coded over the named code context) is transported
to the Gamma-named VF classes along the Gamma-named integration equivalence
of Proposition 7.9, giving a graded semiring isomorphism and its ring
version. No hypothesis puts the common names of `⟨C.base, Ξ⟩` into `C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma-named VF class of the actual lift of a Gamma all-degree RV object. -/
def gammaNamedVFLiftClass : {n : ℕ} → GammaRVObjects 𝔅 𝔖 n → GammaNamedVFClasses hc C Ξ hΞ n
  | 0, U => Quotient.mk _ ⟨zeroLift U.val,zeroLift_gamma ((RVVolumeObject.Gamma.zero_iff U.val).mp U.property)⟩
  | _+1, U => gammaVFVolumeClass hc 𝔇 𝔅 (gammaVolumeLift hc 𝔇 (fun _ h => gamma_named_code_context_base C Ξ hΞ h)
      ⟨U.val,(RVVolumeObject.Gamma.positive_iff U.val).mp U.property⟩)

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem gamma_named_lift_on_class {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    gammaNamedLiftOnClasses hc C Ξ hΞ hGenerated n (gammaNamedRVClass hc C Ξ hΞ U) =
      gammaNamedVFLiftClass hc C Ξ hΞ U := by
  cases n <;> rfl

include hγ hγ1 in
theorem gamma_named_class_integration_lift {n : ℕ} (U : GammaRVObjects 𝔅 𝔖 n) :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1 n
    gammaNamedIntegrationAddEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n (gammaNamedVFLiftClass hc C Ξ hΞ U) =
      gammaNamedRVClass hc C Ξ hΞ U := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1 n
  change (Equiv.ofBijective _ (gamma_named_lift_on_classes_bijective hc C Ξ hΞ hGenerated γ hγ hγ1 n)).symm
    (gammaNamedVFLiftClass hc C Ξ hΞ U) = _
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, gamma_named_lift_on_class]

include hγ hγ1 in
/-- The graded semiring structure on Gamma-named VF classes (transported). -/
def gammaNamedVFClassGradedSemiring :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
    DirectSum.GSemiring (GammaNamedVFClasses hc C Ξ hΞ) := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  exact gradedAddEquivGSemiring (gammaNamedIntegrationAddEquiv hc C Ξ hΞ hGenerated γ hγ hγ1)

include hγ hγ1 in
abbrev GammaNamedVFSemiring : Type := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  exact DirectSum ℕ (GammaNamedVFClasses hc C Ξ hΞ)

include hγ hγ1 in
/-- Gamma-named graded integration as a semiring isomorphism. -/
def gammaNamedGradedIntegrationEquiv :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
    letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
    GammaNamedVFSemiring hc C Ξ hΞ hGenerated γ hγ hγ1 ≃+* GammaNamedRVSemiring hc C Ξ hΞ := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
  exact gradedAddEquivSemiringEquiv (gammaNamedIntegrationAddEquiv hc C Ξ hΞ hGenerated γ hγ hγ1)

include hγ hγ1 in
theorem gamma_named_graded_integration_of (n : ℕ) (a : GammaNamedVFClasses hc C Ξ hΞ n) :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
    letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
    gammaNamedGradedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1
        (DirectSum.of (GammaNamedVFClasses hc C Ξ hΞ) n a) =
      DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n
        (gammaNamedIntegrationAddEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n a) := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
  change DirectSum.map (fun i => (gammaNamedIntegrationAddEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 i).toAddMonoidHom)
    (DirectSum.of (GammaNamedVFClasses hc C Ξ hΞ) n a) = _
  rw [DirectSum.map_of]
  rfl

include hγ hγ1 in
/-- **Gamma-named Theorem 7.10.** A graded VF class integrates to the class of a Gamma
RV object of degree `n` exactly when it is the class of the actual lift of that object. -/
theorem gamma_named_theorem_7_10
    (a : GammaNamedVFSemiring hc C Ξ hΞ hGenerated γ hγ hγ1) (n : ℕ) (U : GammaRVObjects 𝔅 𝔖 n) :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
    letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
    gammaNamedGradedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 a =
        DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n (gammaNamedRVClass hc C Ξ hΞ U) ↔
      a = DirectSum.of (GammaNamedVFClasses hc C Ξ hΞ) n (gammaNamedVFLiftClass hc C Ξ hΞ U) := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
  have h := (gamma_named_graded_integration_of hc C Ξ hΞ hGenerated γ hγ hγ1 n
    (gammaNamedVFLiftClass hc C Ξ hΞ U)).trans
      (congrArg (DirectSum.of (GammaNamedRVClasses hc C Ξ hΞ) n)
        (gamma_named_class_integration_lift hc C Ξ hΞ hGenerated γ hγ hγ1 U))
  rw [← h]
  exact (gammaNamedGradedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1).injective.eq_iff

/-- The Grothendieck ring of Gamma-named RV classes. -/
abbrev GammaNamedRVRing := SemiringGroupification (GammaNamedRVSemiring hc C Ξ hΞ)

include hγ hγ1 in
abbrev GammaNamedVFRing : Type := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
  exact SemiringGroupification (GammaNamedVFSemiring hc C Ξ hΞ hGenerated γ hγ hγ1)

include hγ hγ1 in
/-- Gamma-named integration as a ring isomorphism of Grothendieck rings. -/
def gammaNamedIntegrationRingEquiv :
    letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
    letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
    GammaNamedVFRing hc C Ξ hΞ hGenerated γ hγ hγ1 ≃+* GammaNamedRVRing hc C Ξ hΞ := by
  letI := gammaNamedVFClassesAddCommMonoid hc C Ξ hΞ hGenerated γ hγ hγ1
  letI := gammaNamedVFClassGradedSemiring hc C Ξ hΞ hGenerated γ hγ hγ1
  exact semiringGroupificationEquiv (gammaNamedGradedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1)

end IntegrationInACVF.Section7.HK
