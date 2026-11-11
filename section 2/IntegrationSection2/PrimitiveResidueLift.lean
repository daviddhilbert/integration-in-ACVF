import IntegrationSection2.ResidueIndependentLifts
import Section9.UnramifiedGenerator

/-! A primitive residue generator lifts to a simple integral root
without assuming equality of residue and field degrees.
The polynomial/root calculation is adapted from the checked pinned
Section9/UnramifiedGenerator.lean; residue finiteness is supplied by
the independent-lift argument, not by the desired degree equality. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing Polynomial Module
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.PrimitiveResidueLift

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem exists_lift (v : Valuation K Γ) (F : Subfield K) [FiniteDimensional F K]
    [HenselianLocalRing v.valuationSubring] [CharZero (ResidueField v.valuationSubring)] :
    letI := (residueFieldInclusion v F).toAlgebra
    ∃ pb : PowerBasis (ResidueField (v.comap F.subtype).valuationSubring) (ResidueField v.valuationSubring),
      ∃ u : v.valuationSubring, ∃ P : Polynomial (v.comap F.subtype).valuationSubring,
        P.Monic ∧ P.map (residue (v.comap F.subtype).valuationSubring) = minpoly _ pb.gen ∧
        residue v.valuationSubring u = pb.gen ∧
        (P.map (valuationRingInclusion v F)).IsRoot u := by
  classical
  let A := (v.comap F.subtype).valuationSubring
  let B := v.valuationSubring
  let k := ResidueField A
  let l := ResidueField B
  let j := residueFieldInclusion v F
  letI : Algebra k l := j.toAlgebra
  letI : CharZero k := ⟨by
    intro a b h
    apply (Nat.cast_injective (R := l))
    simpa only [map_natCast] using congrArg j h⟩
  letI : FiniteDimensional k l := ResidueIndependentLifts.residue_finite v F
  letI : Algebra.IsSeparable k l := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let pb : PowerBasis k l := Field.powerBasisOfFiniteOfSeparable k l
  let q := minpoly k pb.gen
  have hq : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hzero : aeval pb.gen q = 0 := minpoly.aeval k pb.gen
  have hsep : q.Separable := (minpoly.irreducible (Algebra.IsIntegral.isIntegral pb.gen)).separable
  have hderiv : aeval pb.gen q.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hzero
  have hqLift : q ∈ lifts (residue A) :=
    ⟨(Polynomial.map_surjective _ residue_surjective q).choose,
      (Polynomial.map_surjective _ residue_surjective q).choose_spec⟩
  obtain ⟨P,hP,_,hPm⟩ := lifts_and_natDegree_eq_and_monic hqLift hq
  let i := valuationRingInclusion v F
  let Q := P.map i
  have hred : Q.map (residue B) = q.map j := by
    change (P.map i).map (residue B) = _
    rw [Polynomial.map_map,← ResidueField.map_comp_residue,← Polynomial.map_map,hP]
    rfl
  have hQzero : aeval pb.gen Q = 0 := by
    rw [Polynomial.aeval_def,ResidueField.algebraMap_eq,← Polynomial.eval_map,hred,Polynomial.eval_map]
    exact hzero
  have hQderiv : aeval pb.gen Q.derivative ≠ 0 := by
    rw [Polynomial.aeval_def,ResidueField.algebraMap_eq,← Polynomial.eval_map,
      ← Polynomial.derivative_map,hred,Polynomial.derivative_map,Polynomial.eval_map]
    exact hderiv
  have hEval (p : Polynomial B) (a : B) : residue B (p.eval a) = aeval (residue B a) p := by
    rw [← Polynomial.eval_map_apply,Polynomial.aeval_def,ResidueField.algebraMap_eq,Polynomial.eval_map]
  obtain ⟨a,ha⟩ := residue_surjective (R := B) pb.gen
  have ha₀ : Q.eval a ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff,hEval,ha]
    exact hQzero
  have haUnit : IsUnit (Q.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit,hEval,ha]
    exact hQderiv
  obtain ⟨u,hu,hua⟩ := HenselianLocalRing.is_henselian Q (hPm.map i) a ha₀ haUnit
  have hres : residue B u = pb.gen := by
    rw [← residue_eq_zero_iff,map_sub,ha,sub_eq_zero] at hua
    exact hua
  exact ⟨pb,u,P,hPm,hP,hres,hu⟩

end IntegrationInACVF.Section2.PrimitiveResidueLift
