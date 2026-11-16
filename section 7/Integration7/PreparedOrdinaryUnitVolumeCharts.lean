module

public import Integration7.ContractionRetainedUnitLabels
public import Integration7.GammaUnitCoordinateDensityCharts
public import Integration7.GammaUnitEmptyVolumeBlockSwaps

@[expose] public section

/-! The prepared ordinary indexed object with a retained unit label
is exactly the literal unit-density object, including its Gamma chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {l a : ℕ}

theorem prepared_ordinary_unit_volume_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (M := M) S 1 0) (Z : DefSet (M := M) S 1 l) (K : SpecialBijection A Z)
    (F : GammaFiniteRVSchema B 1 a 0) (G : GammaFiniteRVSchema B (1+l) a 0 (fun _ => .rv))
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z) (J : G.IndexedPresentation BP)
    (U : DefSet (M := M) S 1 a) (hSource : carrier U = vfSchemaSource (carrier A) F)
    (δ : Fin a) (hUnit : ∀ u : U, (u.val.2 δ).val = iRVOne)
    (hJC : J.codes ⊆ (C.base : Set M))
    (hNZ : ∀ u : rvObjectDomain (gammaSwapVolumeBlocks (n := 1) (e := 0) J.toGamma).object,
      (u.val (Fin.natAdd (1+l) δ)).val ≠ iRVZero) :
    ∃ e : RVVolumeIso
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C
        (gammaSwapVolumeBlocks (n := 1) (e := 0) J.toGamma) hJC (Fin.natAdd (1+l) δ) hNZ)
      (gammaUnitVolumeObject hc C J.toGamma hJC), e.GammaDefinable B := by
  obtain ⟨f,hf⟩ := gamma_unit_coordinate_density_iso hc C
    (gammaSwapVolumeBlocks (n := 1) (e := 0) J.toGamma) hJC (Fin.natAdd (1+l) δ) hNZ (by
      intro u
      apply Subtype.ext
      exact (prepared_indexed_retained_label_unit A Z K F G hRows BP J U hSource δ hUnit
        ⟨u.val,u.property⟩).trans RVOperations.one_val.symm)
  obtain ⟨g,hg⟩ := gamma_unit_empty_volume_block_swap_iso hc C J.toGamma hJC
  exact ⟨(f.symm hc C).trans hc C g,(hf.symm hc C B).trans hc C B hg⟩

end IntegrationInACVF.Section7
