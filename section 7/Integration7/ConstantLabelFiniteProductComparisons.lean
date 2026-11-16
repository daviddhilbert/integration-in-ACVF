module

public import Integration7.UnitDensityRVProducts
public import Integration7.ConstantLabelPreparedVolumeComparisons
public import Integration7.FixedLabelUnarySpecialPreparations

@[expose] public section

/-! Deleting the carried constant labels in either factor of a full
RV product preserves the exact two-coordinate volume and original Gamma.
The unary finiteness assumptions are proved from the actual chains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (SpecialBijection IsRVPullback pullbackObject GammaChainDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {b l : ℕ}

theorem constant_label_prepared_unary_product_isos
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hPC : P.real ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    {T : SpecialBijection A B} (hT : GammaChainDefinable P T.chain)
    (hB : IsRVPullback (SpecialTransformations.Section5.carrier B))
    {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    {t : Fin l → SpecialTransformations.Section5.RV (M := M)}
    (L : ConstantRVLabelSpecialPreparation T H t P)
    (V : RVFiniteObject (M := M) (C.base : Set M) 1) (hVΓ : RVMapGamma V.obj.volume P) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small
    let hLF := constant_label_prepared_pullback_finite_volume C.uncountable.le C.saturated hsmall L
    let hBF := pure_unary_special_pullback_finite_volume C.uncountable.le C.saturated hsmall T hT hB
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    let U' := canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩
    (∃ e : RVVolumeIso (unaryFiniteProductUnitVolume U V) (unaryFiniteProductUnitVolume U' V), e.GammaDefinable P) ∧
      (∃ e : RVVolumeIso (unaryFiniteProductUnitVolume V U) (unaryFiniteProductUnitVolume V U'), e.GammaDefinable P) := by
  intro hsmall hLF hBF U U'
  let e := constantLabelPreparedFiniteRVIso C.uncountable.le C.saturated hsmall hc L hB hLF hBF
  have hValue : ∀ u, U'.obj.value (finiteIsoMap e u) = U.obj.value u := by
    intro u
    funext i
    fin_cases i
    exact constant_label_prepared_finite_rv_iso_value C.uncountable.le C.saturated hsmall hc L hB hLF hBF u
  have heΓ := constant_label_prepared_finite_rv_iso_gamma C.uncountable.le C.saturated hsmall hc L hB hLF hBF
  have hIdΓ : RVMapGamma (finiteIsoMap (Iso.refl V)) P := RVMapGamma.identity hc hVΓ.domain
  have hUΓ : RVMapGamma U.obj.volume P := canonical_gamma_object_volume_graph hc
    (FiniteRV.gammaPullbackAt hPC L.target (L.gamma.target P L.special.chain) hLF)
  exact ⟨⟨unaryFiniteProductUnitVolumeIso hc C e (Iso.refl V) hValue (fun _ => rfl),
      unary_finite_product_unit_volume_iso_gamma hc C e (Iso.refl V) hValue (fun _ => rfl) heΓ hIdΓ hUΓ hVΓ⟩,
    ⟨unaryFiniteProductUnitVolumeIso hc C (Iso.refl V) e (fun _ => rfl) hValue,
      unary_finite_product_unit_volume_iso_gamma hc C (Iso.refl V) e (fun _ => rfl) hValue hIdΓ heΓ hVΓ hUΓ⟩⟩

end IntegrationInACVF.Section7
