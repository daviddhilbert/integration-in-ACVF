import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Residue characteristic zero implies field characteristic zero,
using only the actual valuation subring and residue homomorphism. -/

open IsLocalRing

namespace IntegrationInACVF.Section2.ResidueZeroCharacteristic

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem field_charZero (v : Valuation K Γ) [CharZero (ResidueField v.valuationSubring)] : CharZero K := by
  let A := v.valuationSubring
  letI : CharZero A := ⟨by
    intro m n h
    apply Nat.cast_injective (R := ResidueField A)
    simpa only [map_natCast] using congrArg (residue A) h⟩
  constructor
  intro m n h
  apply Nat.cast_injective (R := A)
  apply Subtype.ext
  change A.subtype (m:A) = A.subtype (n:A)
  simpa only [map_natCast] using h

end IntegrationInACVF.Section2.ResidueZeroCharacteristic
