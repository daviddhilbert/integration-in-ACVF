import IntegrationSection2.HenselianFixedField

/-! Henselianity ascends to intermediate algebraic fields inside an
algebraically closed Galois envelope, in residue characteristic zero.
The proof constructs the restricted base automorphism and uses only
the checked comparison-invariance and fixed-field descent theorems. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing

namespace IntegrationInACVF.Section2.HenselianAlgebraicTower

variable {K Γ : Type*} [Field K] [IsAlgClosed K] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) (F E : Subfield K)

theorem henselian_intermediate [IsGalois F K] [IsGalois E K]
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)] (hFE : F ≤ E) :
    HenselianLocalRing (v.comap E.subtype).valuationSubring := by
  apply HenselianFixedField.henselian_of_comparisons v E
  intro σ x y
  let σF : K ≃ₐ[F] K := {
    toRingEquiv := σ.toRingEquiv
    commutes' c := by
      let cE : E := ⟨c.val,hFE c.property⟩
      exact σ.commutes cE
  }
  exact SpecialTransformations.Section6.henselian_automorphism_invariance v
    (SpecialTransformations.Section6.nat_sub_value_one v) σF x y

theorem automorphism_value_of_base_value [IsGalois F K]
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (σ : K ≃ₐ[F] K) (x : K) (c : F) (hc : v (c:K) = v x) : v (σ x) = v x := by
  have hfix : σ (c:K) = (c:K) := σ.commutes c
  have hcomp := SpecialTransformations.Section6.henselian_automorphism_invariance
    v (SpecialTransformations.Section6.nat_sub_value_one v) σ
  have hle := (hcomp x (c:K)).mpr hc.ge
  have hge := (hcomp (c:K) x).mpr hc.le
  rw [hfix,hc] at hle hge
  exact le_antisymm hle hge

end IntegrationInACVF.Section2.HenselianAlgebraicTower
