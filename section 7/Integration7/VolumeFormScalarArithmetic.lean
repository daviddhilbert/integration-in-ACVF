module

public import Integration7.ScalarRVAlgebra

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Pointwise multiplication and division of actual nonzero definable
densities on one fixed domain. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.VolumeForm
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Space LRV M} {S : Set M} {A : DefSet P S}

def mul (ω η : VolumeForm A) : VolumeForm A where
  map := rvScalarMul ω.map η.map
  nonzero p := mul_ne_zero (ω.nonzero p) (η.nonzero p)

theorem mul_value (ω η : VolumeForm A) (p : A) :
    (ω.mul η).value p = ω.value p * η.value p := rfl

def inv (ω : VolumeForm A) : VolumeForm A where
  map := (rvInverse S).comp ω.map
  nonzero p := inv_ne_zero (ω.nonzero p)

theorem inv_value (ω : VolumeForm A) (p : A) : (ω.inv).value p = (ω.value p)⁻¹ := rfl

def div (ω η : VolumeForm A) : VolumeForm A := ω.mul η.inv

theorem div_value (ω η : VolumeForm A) (p : A) :
    (ω.div η).value p = ω.value p / η.value p := (div_eq_mul_inv _ _).symm

end IntegrationInACVF.Section7.VolumeForm
