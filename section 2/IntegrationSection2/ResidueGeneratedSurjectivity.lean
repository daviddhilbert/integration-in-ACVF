import IntegrationSection2.PrimitiveResidueLift

/-! If an intermediate subfield contains a lift of a primitive
residue generator, its residue inclusion into the upper field is
surjective. Coefficients are lifted from the original base, and
polynomial evaluation stays in the actual residue-field image. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing Polynomial
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.ResidueGeneratedSurjectivity

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem surjective (v : Valuation K Γ) (F E : Subfield K) (hFE : F ≤ E)
    (u : v.valuationSubring) (hu : (u:K) ∈ E) :
    letI := (residueFieldInclusion v F).toAlgebra
    ∀ pb : PowerBasis (ResidueField (v.comap F.subtype).valuationSubring) (ResidueField v.valuationSubring),
      residue v.valuationSubring u = pb.gen → Function.Surjective (residueFieldInclusion v E) := by
  classical
  letI := (residueFieldInclusion v F).toAlgebra
  intro pb hres z
  let A := (v.comap F.subtype).valuationSubring
  let B := v.valuationSubring
  let C := (v.comap E.subtype).valuationSubring
  let jF := residueFieldInclusion v F
  let jE := residueFieldInclusion v E
  let R := jE.fieldRange
  have hbase (a : ResidueField A) : jF a ∈ R := by
    obtain ⟨a₀,ha₀⟩ := residue_surjective (R := A) a
    let aE : C := ⟨⟨((a₀:F):K),hFE (a₀:F).property⟩,a₀.property⟩
    refine ⟨residue C aE,?_⟩
    calc
      _ = residue B (valuationRingInclusion v E aE) := ResidueField.map_residue _ _
      _ = residue B (valuationRingInclusion v F a₀) := congrArg (residue B) (Subtype.ext rfl)
      _ = jF (residue A a₀) := (ResidueField.map_residue _ _).symm
      _ = jF a := congrArg jF ha₀
  have hgen : pb.gen ∈ R := by
    let uE : C := ⟨⟨(u:K),hu⟩,u.property⟩
    refine ⟨residue C uE,?_⟩
    calc
      _ = residue B (valuationRingInclusion v E uE) := ResidueField.map_residue _ _
      _ = residue B u := congrArg (residue B) (Subtype.ext rfl)
      _ = pb.gen := hres
  have hmem (p : Polynomial (ResidueField A)) : aeval pb.gen p ∈ R := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using R.add_mem hp hq
    | monomial n a =>
      simp only [Polynomial.aeval_def,Polynomial.eval₂_monomial,RingHom.algebraMap_toAlgebra]
      exact R.mul_mem (hbase a) (R.pow_mem hgen n)
  obtain ⟨p,hp⟩ := pb.exists_eq_aeval' z
  have hz : z ∈ R := hp ▸ hmem p
  exact hz

end IntegrationInACVF.Section2.ResidueGeneratedSurjectivity
