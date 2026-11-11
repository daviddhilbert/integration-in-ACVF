import IntegrationSection2.EmbeddedAlgebraicHenselian
import IntegrationSection2.FieldDegreeTransport
import IntegrationSection2.ValuedSubfieldRestriction

/-! Every actual intermediate field of a finite embedded extension
over the henselian base has its induced henselian valuation ring. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

namespace IntegrationInACVF.Section2.EmbeddedIntermediateHenselian

variable {D K Γ : Type} [Field D] [Field K] [IsAlgClosed K] [CharZero K]
  [LinearOrderedCommGroupWithZero Γ]

theorem henselian (v : Valuation K Γ) (f : D →+* K) (F : Subfield D)
    [FiniteDimensional F D]
    [HenselianLocalRing ((v.comap f).comap F.subtype).valuationSubring]
    [CharZero (ResidueField v.valuationSubring)] (M : IntermediateField F D) :
    HenselianLocalRing ((v.comap f).comap M.toSubfield.subtype).valuationSubring := by
  let w := v.comap f
  have hFM : F ≤ M.toSubfield := by
    intro x hx
    exact M.algebraMap_mem ⟨x,hx⟩
  let F' := F.comap M.toSubfield.subtype
  let eF := ValuedSubfieldRestriction.fieldEquiv M.toSubfield F hFM
  letI : FiniteDimensional F' M :=
    FieldDegreeTransport.finite_left eF (RingEquiv.refl M) (fun _ _ => rfl)
  let g := f.comp M.toSubfield.subtype
  letI : HenselianLocalRing ((v.comap g).comap F'.subtype).valuationSubring := by
    dsimp only [g]
    rw [Valuation.comap_comp]
    exact (ValuedSubfieldRestriction.henselian_iff w M.toSubfield F hFM).mpr inferInstance
  have hHen := EmbeddedAlgebraicHenselian.henselian v g F'
    (fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic)
  rw [← Valuation.comap_comp]
  exact hHen

end IntegrationInACVF.Section2.EmbeddedIntermediateHenselian
