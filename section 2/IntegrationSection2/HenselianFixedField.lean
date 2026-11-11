import Section6.HenselianInvariance
import Section7.ValuationHenselian
import Mathlib.FieldTheory.Galois.Infinite

/-! Hensel root descent through the fixed field of valuation-preserving
automorphisms. This proves the henselianity part inside an algebraic
closure from checked root lifting, uniqueness and Galois fixed fields. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Classical Polynomial IsLocalRing

namespace IntegrationInACVF.Section2.HenselianFixedField

theorem derivative_unit_of_close {R : Type*} [CommRing R] [IsLocalRing R]
    (f : R[X]) (a b : R) (hba : b-a ∈ maximalIdeal R)
    (ha : IsUnit (f.derivative.eval a)) : IsUnit (f.derivative.eval b) := by
  have he : residue R b = residue R a := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (residue_eq_zero_iff _).mpr hba
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [← Polynomial.eval_map_apply,he,Polynomial.eval_map_apply]
  exact (residue_ne_zero_iff_isUnit _).mpr ha

theorem henselian_of_comparisons {K Γ : Type*} [Field K] [IsAlgClosed K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (F : Subfield K)
    [IsGalois F K]
    (hσ : ∀ σ : K ≃ₐ[F] K, ∀ x y : K, v (σ x) ≤ v (σ y) ↔ v x ≤ v y) :
    HenselianLocalRing (v.comap F.subtype).valuationSubring := by
  classical
  let w := v.comap F.subtype
  let A := w.valuationSubring
  let B := v.valuationSubring
  letI : w.HasExtension v := ⟨fun _ _ => Iff.rfl⟩
  letI : HenselianLocalRing B := SpecialTransformations.Section7.valuationRing_henselian v
  let ι : A →+* B := algebraMap A B
  have hval (a : A) : (ι a : K) = ((a : F) : K) := rfl
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ hfa hda
  let g := f.map ι
  have hEval (a : A) : g.eval (ι a) = ι (f.eval a) := Polynomial.eval_map_apply ι a
  have hg : g.eval (ι a₀) ∈ maximalIdeal B := by
    rw [hEval]
    change f.eval a₀ ∈ (maximalIdeal B).comap ι
    rwa [maximalIdeal_comap]
  have hgd : IsUnit (g.derivative.eval (ι a₀)) := by
    rw [Polynomial.derivative_map,Polynomial.eval_map_apply]
    exact hda.map ι
  obtain ⟨b,hb,hba⟩ := HenselianLocalRing.is_henselian g (hf.map ι) (ι a₀) hg hgd
  have hbunit := derivative_unit_of_close g (ι a₀) b hba hgd
  have hclose : v ((b : K)-((a₀ : F):K)) < 1 :=
    (Valuation.mem_maximalIdeal_iff K v).mp hba
  let p := f.map A.subtype
  have hMaps : g.map B.subtype = p.map F.subtype := by
    dsimp only [g,p]
    rw [Polynomial.map_map,Polynomial.map_map]
    congr 1
  have hEvalB (z : B) : B.subtype (g.eval z) = (p.map F.subtype).eval (z:K) := by
    rw [← Polynomial.eval_map_apply,hMaps]
    rfl
  have hroot : (p.map F.subtype).IsRoot (b : K) := by
    change (p.map F.subtype).eval (b:K) = 0
    rw [← hEvalB,hb,map_zero]
  have hfixed (σ : K ≃ₐ[F] K) : σ (b : K) = (b : K) := by
    have hσsmall (z : K) (hz : v z < 1) : v (σ z) < 1 := by
      apply lt_of_not_ge
      intro hle
      have h := (hσ σ 1 z).mp (by simpa only [map_one] using hle)
      rw [map_one] at h
      exact (not_le_of_gt hz) h
    have hσb : v (σ (b : K)) ≤ 1 := by
      have h := (hσ σ (b : K) 1).mpr (by
        rw [map_one]
        exact (Valuation.mem_valuationSubring_iff v _).mp b.property)
      simpa only [map_one] using h
    let bσ : B := ⟨σ (b : K),(Valuation.mem_valuationSubring_iff v _).mpr hσb⟩
    have hσa : σ (((a₀ : F):K)) = ((a₀ : F):K) := σ.commutes (a₀ : F)
    have hσclose : v ((bσ : K)-((a₀ : F):K)) < 1 := by
      have h := hσsmall ((b:K)-((a₀:F):K)) hclose
      simpa only [map_sub,hσa] using h
    have hrootσ : g.IsRoot bσ := by
      apply Subtype.val_injective
      change B.subtype (g.eval bσ) = 0
      rw [hEvalB]
      change (p.map F.subtype).eval (σ (b:K)) = 0
      rw [← Subfield.algebraMap_ofSubfield F,Polynomial.eval_map_algebraMap,Polynomial.aeval_algHom_apply]
      have hroot' : p.aeval (b:K) = 0 := by
        have h := hroot
        rw [Polynomial.IsRoot,← Subfield.algebraMap_ofSubfield F,Polynomial.eval_map_algebraMap] at h
        exact h
      simpa only [map_zero] using congrArg σ hroot'
    have hdiff : v ((b:K)-(bσ:K)) < 1 := by
      have he : (b:K)-(bσ:K) = ((b:K)-((a₀:F):K))-((bσ:K)-((a₀:F):K)) := by ring
      rw [he]
      exact (v.map_sub _ _).trans_lt (max_lt hclose hσclose)
    have hnonunit : ¬ IsUnit (b-bσ) := by
      rw [← mem_nonunits_iff,← mem_maximalIdeal]
      exact (Valuation.mem_maximalIdeal_iff K v).mpr hdiff
    have he := IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hb hrootσ hnonunit hbunit
    exact (congrArg B.subtype he).symm
  obtain ⟨c,hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (b:K)).mpr hfixed
  change (c:K) = (b:K) at hc
  have hcval : w c ≤ 1 := by
    change v (c:K) ≤ 1
    rw [hc]
    exact (Valuation.mem_valuationSubring_iff v _).mp b.property
  let c₀ : A := ⟨c,(Valuation.mem_valuationSubring_iff w _).mpr hcval⟩
  have hcb : ι c₀ = b := Subtype.ext hc
  refine ⟨c₀,?_,?_⟩
  · apply (show Function.Injective ι from fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg B.subtype hxy)))
    rw [map_zero,← hEval,hcb]
    exact hb
  · rw [← maximalIdeal_comap ι]
    change ι (c₀-a₀) ∈ maximalIdeal B
    rw [map_sub,hcb]
    exact hba

end IntegrationInACVF.Section2.HenselianFixedField
