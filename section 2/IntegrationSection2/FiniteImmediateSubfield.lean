import IntegrationSection2.HenselianImmediateEmbeddings
import IntegrationSection2.ValuedSubfieldRestriction
import IntegrationSection2.AlgebraicEnvelopeBases
import Section9.GaussExtension

/-! No finite immediate extension of a henselian subfield inside
the actual algebraically closed valued ambient field survives in
residue characteristic zero. The finite extension may be non-Galois;
the algebraic Galois envelope is constructed internally. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Classical IsLocalRing IntermediateField
open SpecialTransformations.Section9

namespace IntegrationInACVF.Section2.FiniteImmediateSubfield

variable {K Γ : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem finrank_eq_one (v : Valuation K Γ) (F : Subfield K)
    [HenselianLocalRing (v.comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)]
    (L : IntermediateField F K) [FiniteDimensional F L]
    (h : ∀ x : L, x ≠ 0 → ∃ c : F, v ((x:K)-(c:K)) < v (x:K)) :
    Module.finrank F L = 1 := by
  let C : IntermediateField F K := algebraicClosure F K
  letI : IsAlgClosed C := IsAlgClosure.isAlgClosed F
  have hFC : F ≤ C.toSubfield := by
    intro x hx
    exact C.algebraMap_mem ⟨x,hx⟩
  have hFL : F ≤ L.toSubfield := by
    intro x hx
    exact L.algebraMap_mem ⟨x,hx⟩
  have hLC : L.toSubfield ≤ C.toSubfield := by
    intro x hx
    apply mem_algebraicClosure_iff.mpr
    have hint : IsIntegral F (⟨x,hx⟩:L) := Algebra.IsIntegral.isIntegral _
    exact (hint.map L.val).isAlgebraic
  let w := v.comap C.toSubfield.subtype
  let F' := F.comap C.toSubfield.subtype
  let L' := L.toSubfield.comap C.toSubfield.subtype
  have hF'L' : F' ≤ L' := fun _ hx => hFL hx
  let U : IntermediateField F' C := L'.toIntermediateField (fun c => hF'L' c.property)
  let eF : F' ≃+* F := ValuedSubfieldRestriction.fieldEquiv C.toSubfield F hFC
  let eL : U ≃+* L := ValuedSubfieldRestriction.fieldEquiv C.toSubfield L.toSubfield hLC
  have hRank : Module.rank F' U = Module.rank F L :=
    rank_eq_of_equiv_equiv eF eL.toAddEquiv eF.bijective (fun _ _ => rfl)
  have hfinrank : Module.finrank F' U = Module.finrank F L := congrArg Cardinal.toNat hRank
  letI : FiniteDimensional F' U := FiniteDimensional.of_finrank_pos (by
    rw [hfinrank]
    exact Module.finrank_pos)
  letI : IsGalois F' C := AlgebraicEnvelopeBases.galois_comap F C F le_rfl
  letI : HenselianLocalRing (w.comap F'.subtype).valuationSubring :=
    (ValuedSubfieldRestriction.henselian_iff v C.toSubfield F hFC).mpr inferInstance
  letI : CharZero (ResidueField w.valuationSubring) := residueCharZero_of_subfield v C.toSubfield
  have hU (x : U) (hx : x ≠ 0) : ∃ c : F', w ((x:C)-(c:C)) < w (x:C) := by
    have hxL : eL x ≠ 0 := fun he => hx (eL.injective (he.trans (map_zero eL).symm))
    obtain ⟨c,hc⟩ := h (eL x) hxL
    exact ⟨eF.symm c,hc⟩
  have hdim := HenselianImmediateEmbeddings.finrank_eq_one w F' U hU
  exact hfinrank.symm.trans hdim

end IntegrationInACVF.Section2.FiniteImmediateSubfield
