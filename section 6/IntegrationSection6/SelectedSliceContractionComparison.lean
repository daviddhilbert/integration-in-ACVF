import IntegrationSection6.RawSelectedSliceIsomorphisms
import IntegrationSection6.GammaVolumeSliceIsomorphisms
import IntegrationSection6.GammaExactVolumeSwap
import IntegrationSection6.FiniteSelectedContractionSlices
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Arbitrary actual presentations of selected contraction slices are
isomorphic to ordinary finite contractions of the corresponding source
slices. This concerns RV categories and complete Gamma graphs, not just lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}
variable {U : DefSet (M := M) Set.univ n a} {σ : Equiv.Perm (Fin n)}

theorem selectedSliceContractionComparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)
    (t : Fin k → RV (M := M)) (D : RestrictedStandardData C hU hC ρ t)
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ (n+C.arity) n
      ((gammaVolumeSliceSchema (gammaPrependSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaPrependSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC)).rowVolume (fun j => (t j).val))) :
    Nonempty (GammaRVIso Q.toGamma.toGammaRVObject
      (gammaFiniteContraction hκ hs (small_union_range hκ B.real hreal (fun j => (t j).val))
        (Set.subset_univ _) (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t)
        D.contraction D.gamma).toGammaRVObject) := by
  let R := gammaRawSelectedContraction hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC
  let W := gammaSwapVolumeBlocks R
  obtain ⟨P⟩ := (gammaVolumeSliceSchema W).realize_finiteRow (fun j => (t j).val)
    (fun j => (t j).property) (gammaVolumeSliceSchema_finiteRows W t)
  let f := gammaRawSelectedNormalizationIso hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC
  let hf := gammaRawSelectedNormalizationIso_volume hκ hs hreal (Set.subset_univ _) hU ρ hfin C hC
  let g := gammaSwapExactVolumeIso f hf
  let hg := gammaSwapExactVolumeIso_volume f hf
  let e := gammaVolumeSliceIso g hg t P Q
  let d := gammaRawSelectedSliceRestrictedIso hκ hs hreal hU ρ hfin C hC t D P
  let z := gammaRawFiniteNormalizationIso hκ hs
    (small_union_range hκ B.real hreal (fun j => (t j).val)) (Set.subset_univ _)
    (rvLabelSlice_gamma U hU ρ t) (rvLabelSlice_finite U hU ρ hfin t) D.contraction D.gamma
  exact ⟨gammaIsoTrans (gammaIsoSymm e) (gammaIsoTrans d z)⟩

end IntegrationInACVF.Section6.FiniteRV
