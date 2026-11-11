import IntegrationSection2.FiniteImmediateSubfield
import IntegrationSection2.EmbeddedValuationTransport
import IntegrationSection2.FieldDegreeTransport

/-! The finite immediate-extension theorem for any actual field
embedding into the algebraically closed ambient field. This avoids
identifying an abstract finite extension with a literal subfield by
assumption; both field-image equivalences are constructed. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Classical IsLocalRing IntermediateField

namespace IntegrationInACVF.Section2.FiniteImmediateEmbedded

variable {D K Γ : Type} [Field D] [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem finrank_eq_one (v : Valuation K Γ) (f : D →+* K) (F : Subfield D)
    [FiniteDimensional F D]
    [HenselianLocalRing ((v.comap f).comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (h : ∀ x : D, x ≠ 0 → ∃ c : F, v (f x-f (c:D)) < v (f x)) :
    Module.finrank F D = 1 := by
  let g := f.comp F.subtype
  let B := g.fieldRange
  let L := f.fieldRange
  have hBL : B ≤ L := by
    rintro x ⟨c,hc⟩
    exact ⟨c.val,hc⟩
  let U : IntermediateField B K := L.toIntermediateField (fun c => hBL c.property)
  let eF : F ≃+* B := RingHom.rangeRestrictFieldEquiv g
  let eD : D ≃+* U := RingHom.rangeRestrictFieldEquiv f
  have hScalarMap (c : F) (x : D) : eD (c • x) = eF c • eD x := by
    apply Subtype.ext
    exact map_mul f c.val x
  have hScalar (c : B) (x : U) : eD.symm (c • x) = eF.symm c • eD.symm x := by
    apply eD.injective
    rw [eD.apply_symm_apply,hScalarMap,eF.apply_symm_apply,eD.apply_symm_apply]
  letI : FiniteDimensional B U := FieldDegreeTransport.finite_left eF.symm eD.symm hScalar
  letI : HenselianLocalRing (v.comap B.subtype).valuationSubring :=
    (EmbeddedValuationTransport.henselian_iff v g).mp (by
      dsimp only [g]
      rw [Valuation.comap_comp]
      infer_instance)
  have hU (x : U) (hx : x ≠ 0) : ∃ c : B, v ((x:K)-(c:K)) < v (x:K) := by
    have hxD : eD.symm x ≠ 0 := fun he => hx (eD.symm.injective (he.trans (map_zero eD.symm).symm))
    obtain ⟨c,hc⟩ := h (eD.symm x) hxD
    refine ⟨eF c,?_⟩
    have he : f (eD.symm x) = (x:K) := congrArg Subtype.val (eD.apply_symm_apply x)
    change v ((x:K)-f (c:D)) < v (x:K)
    rwa [he] at hc
  have hdim := FiniteImmediateSubfield.finrank_eq_one v B U hU
  exact (FieldDegreeTransport.finrank eF.symm eD.symm hScalar).symm.trans hdim

end IntegrationInACVF.Section2.FiniteImmediateEmbedded
