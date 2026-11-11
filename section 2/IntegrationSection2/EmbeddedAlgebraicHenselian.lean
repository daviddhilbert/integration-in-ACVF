import IntegrationSection2.AlgebraicSubfieldHenselian
import IntegrationSection2.EmbeddedValuationTransport

/-! Algebraic henselian ascent through an arbitrary actual embedding
into the algebraically closed ambient valued field. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical IsLocalRing

namespace IntegrationInACVF.Section2.EmbeddedAlgebraicHenselian

variable {D K Γ : Type} [Field D] [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem henselian (v : Valuation K Γ) (f : D →+* K) (F : Subfield D)
    [HenselianLocalRing ((v.comap f).comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)] (hAlg : ∀ x : D, IsAlgebraic F x) :
    HenselianLocalRing (v.comap f).valuationSubring := by
  let g := f.comp F.subtype
  let B := g.fieldRange
  let L := f.fieldRange
  let eF := RingHom.rangeRestrictFieldEquiv g
  letI : Algebra F K := g.toAlgebra
  letI : Algebra F B := eF.toRingHom.toAlgebra
  letI : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq' (by ext x;rfl)
  let fAlg : D →ₐ[F] K := { f with commutes' _ := rfl }
  have hBL : B ≤ L := by
    rintro x ⟨c,hc⟩
    exact ⟨c.val,hc⟩
  have hL (x : K) (hx : x ∈ L) : IsAlgebraic B x := by
    obtain ⟨d,rfl⟩ := hx
    have hi : IsIntegral F d := (hAlg d).isIntegral
    have hm : IsAlgebraic F (fAlg d) := (hi.map fAlg).isAlgebraic
    exact hm.tower_top B
  letI : HenselianLocalRing (v.comap B.subtype).valuationSubring :=
    (EmbeddedValuationTransport.henselian_iff v g).mp (by
      dsimp only [g]
      rw [Valuation.comap_comp]
      infer_instance)
  letI : HenselianLocalRing (v.comap L.subtype).valuationSubring :=
    AlgebraicSubfieldHenselian.algebraic_henselian v B L hBL hL
  exact (EmbeddedValuationTransport.henselian_iff v f).mpr inferInstance

end IntegrationInACVF.Section2.EmbeddedAlgebraicHenselian
