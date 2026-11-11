import IntegrationSection2.HenselianAlgebraicTower
import Mathlib.RingTheory.Trace.Basic

/-! The trace argument for finite immediate extensions need not assume
that the extension is Galois. Each embedding into the algebraically
closed Galois envelope is extended to an actual automorphism there. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing
open scoped BigOperators

namespace IntegrationInACVF.Section2.HenselianImmediateEmbeddings

variable {K Γ : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (F : Subfield K)
  [IsGalois F K] [HenselianLocalRing (v.comap F.subtype).valuationSubring]
  [CharZero (ResidueField v.valuationSubring)]

theorem embedding_value (E : IntermediateField F K)
    (hSame : ∀ x : E, ∃ c : F, v (c:K) = v (x:K))
    (φ : E →ₐ[F] K) (x : E) : v (φ x) = v (x:K) := by
  let τ : K ≃ₐ[F] K := AlgEquiv.ofBijective (φ.liftNormal K) (AlgHom.normal_bijective F K K _)
  have he : τ (x:K) = φ x := φ.liftNormal_commutes K x
  obtain ⟨c,hc⟩ := hSame x
  rw [← he]
  exact HenselianAlgebraicTower.automorphism_value_of_base_value v F τ (x:K) c hc

theorem trace_kernel_zero (E : IntermediateField F K) [FiniteDimensional F E]
    (h : ∀ x : E, x ≠ 0 → ∃ c : F, v ((x:K)-(c:K)) < v (x:K))
    (x : E) (hx : Algebra.trace F E x = 0) : x = 0 := by
  classical
  by_contra hx0
  have hSame (z : E) : ∃ c : F, v (c:K) = v (z:K) := by
    by_cases hz : z = 0
    · exact ⟨0,by rw [hz];rfl⟩
    obtain ⟨c,hc⟩ := h z hz
    refine ⟨c,?_⟩
    simpa only [sub_sub_cancel] using v.map_sub_eq_of_lt_left hc
  letI : Nonempty (E →ₐ[F] K) := ⟨E.val⟩
  obtain ⟨c,hc⟩ := h x hx0
  have hcval : v (c:K) = v (x:K) := by
    simpa only [sub_sub_cancel] using v.map_sub_eq_of_lt_left hc
  have hsum : ∑ φ : E →ₐ[F] K, φ x = 0 := by
    rw [← trace_eq_sum_embeddings K (x := x),hx,map_zero]
  have hsmall : v (∑ φ : E →ₐ[F] K, (φ x-(c:K))) < v (x:K) := by
    apply v.map_sum_lt (v.ne_zero_iff.mpr (fun he => hx0 (Subtype.ext he)))
    intro φ _
    have he := embedding_value v F E hSame φ (x-algebraMap F E c)
    have hd : ((x-algebraMap F E c : E):K) = (x:K)-(c:K) := rfl
    rw [hd] at he
    have he' : v (φ x-(c:K)) = v ((x:K)-(c:K)) := by
      simpa only [map_sub,AlgHom.commutes,IntermediateField.algebraMap_apply,
        Subfield.algebraMap_ofSubfield,Subfield.subtype_apply] using he
    exact he'.trans_lt hc
  have he : (∑ φ : E →ₐ[F] K, (φ x-(c:K))) =
      -((Fintype.card (E →ₐ[F] K):ℕ):K)*(c:K) := by
    rw [Finset.sum_sub_distrib,hsum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,zero_sub,neg_mul]
  have hnat : v ((Fintype.card (E →ₐ[F] K):ℕ):K) = 1 := by
    simpa only [Nat.cast_zero,sub_zero] using
      SpecialTransformations.Section6.nat_sub_value_one v (Fintype.card (E →ₐ[F] K)) 0 Fintype.card_ne_zero
  rw [he,map_mul,Valuation.map_neg,hnat,one_mul,hcval] at hsmall
  exact (lt_irrefl _) hsmall

theorem finrank_eq_one (E : IntermediateField F K) [FiniteDimensional F E]
    (h : ∀ x : E, x ≠ 0 → ∃ c : F, v ((x:K)-(c:K)) < v (x:K)) :
    Module.finrank F E = 1 := by
  have hinj : Function.Injective (Algebra.trace F E) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply trace_kernel_zero v F E h
    rw [map_sub,hxy,sub_self]
  have hle : Module.finrank F E ≤ 1 := by
    simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective hinj
  exact hle.antisymm (Nat.succ_le_iff.mpr Module.finrank_pos)

end IntegrationInACVF.Section2.HenselianImmediateEmbeddings
