module

public import Integration7.RVClassProductRawVolumeObjects
public import Integration7.ConstantLabelPreparedFiniteness

@[expose] public section

/-! A supplied actual unary special preparation constructs an actual
two-coordinate product standard contraction and its original-Gamma
volume comparison. All target finiteness is derived from the source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}

theorem rv_class_product_standard_volume_preparation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hT : GammaChainDefinable P T.chain) (hB' : IsRVPullback (carrier B'))
    (hA : GammaSetDefinable P (carrier A)) (r : RV (M := M)) (hr : r.val ∈ S)
    (hProduct : ∀ p : Point (M := M) 2 0, p ∈ carrier A ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier B)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (hTuple : DefinableOverBase P (fun _ : Fin d => .rv) {fun i => (t i).val})
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    ∃ L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P,
    let hLF := constant_label_prepared_pullback_finite_volume hκ hs hsmall L
    let hSat := head_saturated_rv_class_product A B r hProduct
    ∃ e : RVVolumeIso
      ((rvClassProductRawVolumeObject hc A B B' T hSat r hr t ht L hLF).rescale η hη hη0)
      ((prependFixedRVVolume (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr
        (VolumeForm.one _)).rescale η hη hη0), e.GammaDefinable P := by
  obtain ⟨L⟩ := gamma_rv_class_product_tail_preparation_exists A B B' T hT hB' hA r hProduct t ht hTuple
  exact ⟨L,rv_class_product_raw_volume_comparison hc A B B' T
    (head_saturated_rv_class_product A B r hProduct) r hr t ht L
    (constant_label_prepared_pullback_finite_volume hκ hs hsmall L) hPS η hη hη0⟩

end IntegrationInACVF.Section7
