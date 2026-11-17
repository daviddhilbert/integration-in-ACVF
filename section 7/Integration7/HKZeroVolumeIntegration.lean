module

public import Integration7.HKZeroVolumeLiftSurjectivity
public import Integration7.PositiveVolumeIntegrationEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The corrected zero lift is a bijection of actual weighted classes.
Together with the unchanged positive classification, this gives the
all-degree class equivalence under weighted measured degree zero.
Additive and graded-ring assembly are separate obligations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroLiftOnClasses (S : Set M) : ZeroRVVolumeClasses (M := M) S → ZeroVFVolumeClasses (M := M) S :=
  Quotient.lift (fun U => Quotient.mk _ (zeroLift U)) (fun _ _ ⟨e⟩ => Quotient.sound ⟨zeroLiftIso e⟩)

theorem zeroLiftOnClasses_bijective (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Bijective (zeroLiftOnClasses (M := M) (C.base : Set M)) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h U =>
      induction b using Quotient.inductionOn with
      | h V =>
        intro he
        obtain ⟨e⟩ := Quotient.exact he
        exact Quotient.sound ⟨zeroRVOfLiftIso e⟩
  · intro a
    induction a using Quotient.inductionOn with
    | h A =>
      obtain ⟨U,⟨e⟩⟩ := zero_volume_lift_presentation_exists hc C A
      exact ⟨Quotient.mk _ U,Quotient.sound ⟨e.symm⟩⟩

def zeroVolumeIntegrationEquiv (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    ZeroVFVolumeClasses (M := M) (C.base : Set M) ≃ ZeroRVVolumeClasses (M := M) (C.base : Set M) :=
  (Equiv.ofBijective (zeroLiftOnClasses (C.base : Set M)) (zeroLiftOnClasses_bijective hc C)).symm

theorem zero_integration_lift (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    zeroVolumeIntegrationEquiv hc C (Quotient.mk _ (zeroLift U)) = Quotient.mk _ U :=
  (Equiv.ofBijective (zeroLiftOnClasses (C.base : Set M))
    (zeroLiftOnClasses_bijective hc C)).symm_apply_apply (Quotient.mk _ U)

abbrev VFVolumeObject (S : Set M) : ℕ → Type
  | 0 => ZeroVFVolumeObject (M := M) S
  | k+1 => PositiveVFVolumeObject (M := M) S k

def volumeLift (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n → VFVolumeObject (M := M) S n
  | 0,U => zeroLift U
  | _+1,U => rvVolumeLift U

abbrev VFVolumeClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : ℕ → Type
  | 0 => ZeroVFVolumeClasses (M := M) (C.base : Set M)
  | k+1 => PositiveVFVolumeIsoClasses hc C k

abbrev RVVolumeBlowupClasses (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) : ℕ → Type
  | 0 => ZeroRVVolumeClasses (M := M) (C.base : Set M)
  | k+1 => PositiveVolumeBlowupClasses hc C k

def vfClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (n : ℕ) → VFVolumeObject (M := M) (C.base : Set M) n → VFVolumeClasses hc C n
  | 0,A => Quotient.mk _ A
  | _+1,A => positiveVFVolumeIsoClass hc C A

def rvClass (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    (n : ℕ) → RVVolumeObject (M := M) (C.base : Set M) n → RVVolumeBlowupClasses hc C n
  | 0,U => Quotient.mk _ U
  | _+1,U => positiveVolumeBlowupClass hc C U

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def volumeIntegrationEquiv (n : ℕ) : VFVolumeClasses hc C n ≃ RVVolumeBlowupClasses hc C n := by
  cases n with
  | zero => exact zeroVolumeIntegrationEquiv hc C
  | succ k => exact (positiveVolumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1).toEquiv

theorem volume_integration_lift (n : ℕ) (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    volumeIntegrationEquiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (vfClass hc C n (volumeLift (C.base : Set M) n U)) = rvClass hc C n U := by
  cases n with
  | zero => exact zero_integration_lift hc C U
  | succ k => exact (proposition_7_9_positive hc C Ξ hΞ hGenerated hNames γ hγ hγ1 (rvVolumeLift U) U).mpr rfl

end IntegrationInACVF.Section7.HK
