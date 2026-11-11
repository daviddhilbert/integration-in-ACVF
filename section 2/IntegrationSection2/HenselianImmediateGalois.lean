import Section6.HenselianInvariance
import Mathlib.RingTheory.Trace.Basic

/-! An independently proved part of the remaining finite-extension
input: a finite Galois immediate extension of a henselian valued
field of residue characteristic zero is trivial. The proof uses the
already checked henselian automorphism comparison theorem and a
trace-zero averaging argument, not the finite-extension reference. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing
open scoped BigOperators

namespace IntegrationInACVF.Section2.HenselianImmediateGalois

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation L Γ) (F : Subfield L)

def ImmediateApproximation : Prop :=
  ∀ x : L, x ≠ 0 → ∃ c : F, v (x - (c : L)) < v x

theorem same_values (h : ImmediateApproximation v F) (x : L) :
    ∃ c : F, v (c : L) = v x := by
  by_cases hx : x = 0
  · exact ⟨0,by rw [hx];rfl⟩
  obtain ⟨c,hc⟩ := h x hx
  refine ⟨c,?_⟩
  simpa only [sub_sub_cancel] using v.map_sub_eq_of_lt_left hc

theorem automorphism_value [IsGalois F L]
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (h : ∀ x : L, ∃ c : F, v (c : L) = v x)
    (σ : L ≃ₐ[F] L) (x : L) : v (σ x) = v x := by
  obtain ⟨c,hc⟩ := h x
  have hfix : σ (c : L) = (c : L) := σ.commutes c
  have hcomp := SpecialTransformations.Section6.henselian_automorphism_invariance
    v (SpecialTransformations.Section6.nat_sub_value_one v) σ
  have hle := (hcomp x (c : L)).mpr hc.ge
  have hge := (hcomp (c : L) x).mpr hc.le
  rw [hfix,hc] at hle hge
  exact le_antisymm hle hge

theorem trace_kernel_zero [IsGalois F L] [FiniteDimensional F L]
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (h : ImmediateApproximation v F) (x : L) (hx : Algebra.trace F L x = 0) : x = 0 := by
  classical
  by_contra hx0
  obtain ⟨c,hc⟩ := h x hx0
  have hcval : v (c : L) = v x := by
    simpa only [sub_sub_cancel] using v.map_sub_eq_of_lt_left hc
  have hsum : ∑ σ : L ≃ₐ[F] L, σ x = 0 := by
    rw [← trace_eq_sum_automorphisms (K := F) x,hx,map_zero]
  have hsmall : v (∑ σ : L ≃ₐ[F] L, (σ x - (c : L))) < v x := by
    apply v.map_sum_lt (v.ne_zero_iff.mpr hx0)
    intro σ _
    have hfix : σ (c : L) = (c : L) := σ.commutes c
    have he := automorphism_value v F (same_values v F h) σ (x-(c:L))
    rw [map_sub,hfix] at he
    exact he.trans_lt hc
  have he : (∑ σ : L ≃ₐ[F] L, (σ x - (c : L))) =
      -((Fintype.card (L ≃ₐ[F] L) : ℕ) : L) * (c : L) := by
    rw [Finset.sum_sub_distrib,hsum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,zero_sub,neg_mul]
  have hnat : v ((Fintype.card (L ≃ₐ[F] L) : ℕ) : L) = 1 := by
    simpa only [Nat.cast_zero,sub_zero] using
      SpecialTransformations.Section6.nat_sub_value_one v (Fintype.card (L ≃ₐ[F] L)) 0 Fintype.card_ne_zero
  rw [he,map_mul,Valuation.map_neg,hnat,one_mul,hcval] at hsmall
  exact (lt_irrefl _) hsmall

theorem finrank_eq_one [IsGalois F L] [FiniteDimensional F L]
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (h : ImmediateApproximation v F) : Module.finrank F L = 1 := by
  have hinj : Function.Injective (Algebra.trace F L) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply trace_kernel_zero v F h
    rw [map_sub,hxy,sub_self]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hle' : Module.finrank F L ≤ 1 := by simpa only [Module.finrank_self] using hle
  exact hle'.antisymm
    (Nat.succ_le_iff.mpr Module.finrank_pos)

end IntegrationInACVF.Section2.HenselianImmediateGalois
