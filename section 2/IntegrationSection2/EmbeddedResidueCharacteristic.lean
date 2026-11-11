import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Residue characteristic zero passes to an embedded valued subfield
through the actual injective residue homomorphism. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace IntegrationInACVF.Section2.EmbeddedResidueCharacteristic

variable {D K Γ : Type} [Field D] [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem charZero (v : Valuation K Γ) (f : D →+* K)
    [CharZero (ResidueField v.valuationSubring)] :
    CharZero (ResidueField (v.comap f).valuationSubring) := by
  letI : Algebra D K := f.toAlgebra
  let w := v.comap f
  letI : w.HasExtension v := ⟨fun _ _ => Iff.rfl⟩
  let j := ResidueField.map (algebraMap w.valuationSubring v.valuationSubring)
  constructor
  intro m n h
  apply Nat.cast_injective (R := ResidueField v.valuationSubring)
  simpa only [map_natCast] using congrArg j h

end IntegrationInACVF.Section2.EmbeddedResidueCharacteristic
