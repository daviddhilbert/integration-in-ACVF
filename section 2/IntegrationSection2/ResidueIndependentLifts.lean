import Section9.GaussEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Residue-independent integral families lift to field-linearly
independent families. Hence the residue degree of a finite valued
extension is finite and no larger than its field degree.

The normalization calculation generalizes the checked argument in
Special transformations, Section9/ValuedPowerBasis.lean, pinned at
9cc9760892092dd34cfad4a6dee655843c52f30c. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing Module
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section2.ResidueIndependentLifts

variable {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) (F : Subfield K)

theorem residue_nonzero_iff_value_one (a : v.valuationSubring) :
    residue v.valuationSubring a ≠ 0 ↔ v (a:K) = 1 := by
  have ha : v (a:K) ≤ 1 := (Valuation.mem_valuationSubring_iff v _).mp a.property
  rw [ne_eq,residue_eq_zero_iff,Valuation.mem_maximalIdeal_iff,not_lt]
  exact ⟨fun h => le_antisymm ha h,fun h => h.ge⟩

theorem coefficient_le (u : ι → v.valuationSubring) (s : Finset ι)
    (hInd : ∀ c : ι → ResidueField (v.comap F.subtype).valuationSubring,
      (∑ j ∈ s, residueFieldInclusion v F (c j) * residue v.valuationSubring (u j)) = 0 →
        ∀ i ∈ s, c i = 0)
    (c : ι → F) (i : ι) (hi : i ∈ s) :
    v (c i : K) ≤ v (∑ j ∈ s, (c j : K) * (u j : K)) := by
  classical
  let w := v.comap F.subtype
  let A := w.valuationSubring
  let B := v.valuationSubring
  let f : A →+* B := valuationRingInclusion v F
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image s (fun j => w (c j)) ⟨i,hi⟩
  by_cases hc : c m = 0
  · have h := hmax i hi
    rw [hc,map_zero] at h
    exact h.trans zero_le
  let a (j : ι) : A := if hj : j ∈ s then
    ⟨c j / c m,(Valuation.mem_valuationSubring_iff w _).mpr (by
      rw [map_div₀]
      exact (div_le_one₀ (pos_iff_ne_zero.mpr (w.ne_zero_iff.mpr hc))).mpr (hmax j hj))⟩ else 0
  have ha (j : ι) (hj : j ∈ s) : (a j : F) = c j / c m := by simp only [a,dif_pos hj]
  have ham : a m = 1 := Subtype.ext ((ha m hm).trans (div_self hc))
  let q : B := ∑ j ∈ s, f (a j) * u j
  have hqunit : v (q:K) = 1 := by
    apply (residue_nonzero_iff_value_one v q).mp
    intro hz
    have he : (∑ j ∈ s, residueFieldInclusion v F (residue A (a j)) * residue B (u j)) = 0 := by
      have hmap (j : ι) : residueFieldInclusion v F (residue A (a j)) = residue B (f (a j)) :=
        ResidueField.map_residue f (a j)
      calc
        _ = ∑ j ∈ s, residue B (f (a j)) * residue B (u j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hmap j]
        _ = residue B q := by simp only [q,map_sum,map_mul]
        _ = 0 := hz
    have hzero := hInd (fun j => residue A (a j)) he m hm
    exact one_ne_zero (by simpa only [ham,map_one] using hzero)
  have he : (∑ j ∈ s, (c j : K) * (u j : K)) = (c m : K) * (q:K) := by
    change _ = (c m : K) * B.subtype (∑ j ∈ s, f (a j) * u j)
    rw [map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul,← mul_assoc]
    change _ = (c m : K) * ((a j : F):K) * (u j : K)
    rw [ha j hj]
    change _ = (c m : K) * ((c j : K)/(c m:K)) * (u j:K)
    rw [mul_comm (c m:K),div_mul_cancel₀ _ (fun h => hc (Subtype.ext h))]
  rw [he,map_mul,hqunit,mul_one]
  exact hmax i hi

theorem independent (u : ι → v.valuationSubring)
    (hInd : letI := (residueFieldInclusion v F).toAlgebra
      LinearIndependent (ResidueField (v.comap F.subtype).valuationSubring)
        (fun i => residue v.valuationSubring (u i))) :
    LinearIndependent F (fun i => (u i : K)) := by
  letI := (residueFieldInclusion v F).toAlgebra
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  have hbound := coefficient_le v F u s (fun a ha =>
    (linearIndependent_iff'.mp hInd) s a (by
      simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra] using ha)) c i hi
  have hsum' : (∑ j ∈ s, (c j : K) * (u j : K)) = 0 := by
    have he (j : ι) : (c j : K) * (u j : K) = c j • (u j : K) := rfl
    simp_rw [he]
    exact hsum
  rw [hsum',map_zero,le_zero_iff] at hbound
  by_contra hc
  exact (v.ne_zero_iff.mpr (fun he => hc (Subtype.ext he))) hbound

theorem residue_finite [FiniteDimensional F K] :
    letI := (residueFieldInclusion v F).toAlgebra
    FiniteDimensional (ResidueField (v.comap F.subtype).valuationSubring) (ResidueField v.valuationSubring) := by
  letI := (residueFieldInclusion v F).toAlgebra
  let k := ResidueField (v.comap F.subtype).valuationSubring
  let l := ResidueField v.valuationSubring
  let b := Basis.ofVectorSpace k l
  let u (i : Basis.ofVectorSpaceIndex k l) : v.valuationSubring := (residue_surjective (b i)).choose
  have hu : (fun i => residue v.valuationSubring (u i)) = b :=
    funext fun i => (residue_surjective (b i)).choose_spec
  have hLI := independent v F u (by rw [hu];exact b.linearIndependent)
  letI := hLI.finite
  exact b.finiteDimensional_of_finite

theorem residue_finrank_le [FiniteDimensional F K] :
    letI := (residueFieldInclusion v F).toAlgebra
    Module.finrank (ResidueField (v.comap F.subtype).valuationSubring) (ResidueField v.valuationSubring) ≤
      Module.finrank F K := by
  letI := (residueFieldInclusion v F).toAlgebra
  letI := residue_finite v F
  let k := ResidueField (v.comap F.subtype).valuationSubring
  let l := ResidueField v.valuationSubring
  let b := Basis.ofVectorSpace k l
  let u (i : Basis.ofVectorSpaceIndex k l) : v.valuationSubring := (residue_surjective (b i)).choose
  have hu : (fun i => residue v.valuationSubring (u i)) = b :=
    funext fun i => (residue_surjective (b i)).choose_spec
  have hLI := independent v F u (by rw [hu];exact b.linearIndependent)
  letI := FiniteDimensional.fintypeBasisIndex b
  rw [Module.finrank_eq_card_basis b]
  exact hLI.fintype_card_le_finrank

end IntegrationInACVF.Section2.ResidueIndependentLifts
