module

public import Integration7.ConstantLabelPreparedFiniteness
public import Integration7.FixedHeadUnaryVolumeIsomorphisms
public import Integration7.FixedTailUnaryVolumeIsomorphisms
public import Integration7.GammaCoordinateDensityGraphs
public import Integration7.GammaVolumeDensityRescaling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual product volume comparison from a constant-label lifted
unary preparation to its original unary target. Both finite-volume
certificates are proved from the actual special bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {t : Fin l → RV (M := M)}

theorem constant_label_prepared_product_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (hPS : P.real ⊆ S)
    (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B))
    (L : ConstantRVLabelSpecialPreparation T H t P)
    (r : RV (M := M)) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let hLF := constant_label_prepared_pullback_finite_volume hκ hs hsmall L
    let hBF := gamma_special_pullback_finite_volume hκ hs hsmall T hT hB (fun _ => Set.toFinite _)
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩
    ∃ e : RVVolumeIso
      ((prependFixedRVVolume U r hr (VolumeForm.one _)).rescale η hη hη0)
      ((prependFixedRVVolume V r hr (VolumeForm.one _)).rescale η hη hη0), e.GammaDefinable P := by
  intro hLF hBF U V
  let e := constantLabelPreparedFiniteRVIso hκ hs hsmall hc L hB hLF hBF
  let F := finiteIsoMap e
  have hF := finiteIsoMap_bijective e
  have hValue := constant_label_prepared_finite_rv_iso_value hκ hs hsmall hc L hB hLF hBF
  have hUE := gamma_essential_volume_domain (⟨U,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S 0)
    (canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPS L.target
      (GammaChainDefinable.target P L.special.chain L.gamma) hLF))
  let i := fixedHeadUnaryVolumeIso U V r hr F hF hValue (VolumeForm.one _) (VolumeForm.one _) (fun _ => rfl)
  have hi := fixed_head_unary_volume_iso_gamma U V r hr hr0 F hF hValue
    (VolumeForm.one _) (VolumeForm.one _) (fun _ => rfl) hUE
    (constant_label_prepared_finite_rv_iso_gamma hκ hs hsmall hc L hB hLF hBF)
  exact ⟨i.rescale η hη hη0,hi.rescale η hη hη0⟩

theorem constant_label_prepared_tail_product_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (hPS : P.real ⊆ S)
    (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B))
    (L : ConstantRVLabelSpecialPreparation T H t P)
    (r : RV (M := M)) (hr : r.val ∈ S) (hr0 : r.val ≠ iRVZero)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let hLF := constant_label_prepared_pullback_finite_volume hκ hs hsmall L
    let hBF := gamma_special_pullback_finite_volume hκ hs hsmall T hT hB (fun _ => Set.toFinite _)
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩
    ∃ e : RVVolumeIso
      ((appendFixedRVVolume U r hr (VolumeForm.one _)).rescale η hη hη0)
      ((appendFixedRVVolume V r hr (VolumeForm.one _)).rescale η hη hη0), e.GammaDefinable P := by
  intro hLF hBF U V
  let e := constantLabelPreparedFiniteRVIso hκ hs hsmall hc L hB hLF hBF
  let F := finiteIsoMap e
  have hF := finiteIsoMap_bijective e
  have hValue := constant_label_prepared_finite_rv_iso_value hκ hs hsmall hc L hB hLF hBF
  have hUE := gamma_essential_volume_domain (⟨U,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S 0)
    (canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPS L.target
      (GammaChainDefinable.target P L.special.chain L.gamma) hLF))
  let i := fixedTailUnaryVolumeIso U V r hr F hF hValue (VolumeForm.one _) (VolumeForm.one _) (fun _ => rfl)
  have hi := fixed_tail_unary_volume_iso_gamma U V r hr hr0 F hF hValue
    (VolumeForm.one _) (VolumeForm.one _) (fun _ => rfl) hUE
    (constant_label_prepared_finite_rv_iso_gamma hκ hs hsmall hc L hB hLF hBF)
  exact ⟨i.rescale η hη hη0,hi.rescale η hη hη0⟩

end IntegrationInACVF.Section7
