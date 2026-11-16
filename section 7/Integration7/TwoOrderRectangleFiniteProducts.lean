module

public import Integration7.TwoOrderRectanglePreparations
public import Integration7.FixedNativeRectangleRawIsomorphisms
public import Integration7.UnitDensityRVProducts
public import Integration7.ConstantLabelPreparedVolumeComparisons
public import Integration7.FixedLabelUnarySpecialPreparations

@[expose] public section

/-! The actual raw objects of both rectangle programs map to the same
finite unary product, preserving each VF volume coordinate and Gamma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (pullbackObject)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.TwoOrderRectanglePreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hPC : P.real ⊆ (C.base : Set M))
variable {D E : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
variable {z : Fin d → SpecialTransformations.Section5.RV (M := M)} {hz : ∀ j, (z j).val ∈ (C.base : Set M)}
variable (F : TwoOrderRectanglePreparations D E z hz P)

private def small_real : Cardinal.mk P.real < C.κ := (Cardinal.mk_le_mk_of_subset hPC).trans_lt C.small

private def dFiniteNative := pure_unary_special_pullback_finite_volume C.uncountable.le C.saturated (small_real C hPC)
  F.dSpecial F.dGamma F.dPullback
private def eFiniteNative := pure_unary_special_pullback_finite_volume C.uncountable.le C.saturated (small_real C hPC)
  F.eSpecial F.eGamma F.ePullback
private def dFixedFiniteNative := constant_label_prepared_pullback_finite_volume C.uncountable.le C.saturated (small_real C hPC) F.dFixed
private def eFixedFiniteNative := constant_label_prepared_pullback_finite_volume C.uncountable.le C.saturated (small_real C hPC) F.eFixed

def dFinite : RVFiniteObject (M := M) (C.base : Set M) 1 :=
  canonicalFiniteRVObject hc ⟨pullbackObject F.dTarget,dFiniteNative C hPC F⟩
def eFinite : RVFiniteObject (M := M) (C.base : Set M) 1 :=
  canonicalFiniteRVObject hc ⟨pullbackObject F.eTarget,eFiniteNative C hPC F⟩
def dFixedFinite : RVFiniteObject (M := M) (C.base : Set M) 1 :=
  canonicalFiniteRVObject hc ⟨pullbackObject F.dFixed.target,dFixedFiniteNative C hPC F⟩
def eFixedFinite : RVFiniteObject (M := M) (C.base : Set M) 1 :=
  canonicalFiniteRVObject hc ⟨pullbackObject F.eFixed.target,eFixedFiniteNative C hPC F⟩

def dLabelIso : F.dFixedFinite hc C hPC ≅ F.dFinite hc C hPC :=
  constantLabelPreparedFiniteRVIso C.uncountable.le C.saturated (small_real C hPC) hc F.dFixed F.dPullback
    (dFixedFiniteNative C hPC F) (dFiniteNative C hPC F)
def eLabelIso : F.eFixedFinite hc C hPC ≅ F.eFinite hc C hPC :=
  constantLabelPreparedFiniteRVIso C.uncountable.le C.saturated (small_real C hPC) hc F.eFixed F.ePullback
    (eFixedFiniteNative C hPC F) (eFiniteNative C hPC F)

theorem d_label_iso_value : ∀ u, (F.dFinite hc C hPC).obj.value (finiteIsoMap (F.dLabelIso hc C hPC) u) =
    (F.dFixedFinite hc C hPC).obj.value u := by
  intro u
  funext i
  fin_cases i
  exact constant_label_prepared_finite_rv_iso_value C.uncountable.le C.saturated (small_real C hPC) hc
    F.dFixed F.dPullback (dFixedFiniteNative C hPC F) (dFiniteNative C hPC F) u

theorem e_label_iso_value : ∀ u, (F.eFinite hc C hPC).obj.value (finiteIsoMap (F.eLabelIso hc C hPC) u) =
    (F.eFixedFinite hc C hPC).obj.value u := by
  intro u
  funext i
  fin_cases i
  exact constant_label_prepared_finite_rv_iso_value C.uncountable.le C.saturated (small_real C hPC) hc
    F.eFixed F.ePullback (eFixedFiniteNative C hPC F) (eFiniteNative C hPC F) u

theorem d_label_iso_gamma : RVMapGamma (finiteIsoMap (F.dLabelIso hc C hPC)) P :=
  constant_label_prepared_finite_rv_iso_gamma C.uncountable.le C.saturated (small_real C hPC) hc
    F.dFixed F.dPullback (dFixedFiniteNative C hPC F) (dFiniteNative C hPC F)
theorem e_label_iso_gamma : RVMapGamma (finiteIsoMap (F.eLabelIso hc C hPC)) P :=
  constant_label_prepared_finite_rv_iso_gamma C.uncountable.le C.saturated (small_real C hPC) hc
    F.eFixed F.ePullback (eFixedFiniteNative C hPC F) (eFiniteNative C hPC F)

theorem d_finite_volume_gamma : RVMapGamma (F.dFinite hc C hPC).obj.volume P :=
  canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPC F.dTarget (F.dGamma.target P F.dSpecial.chain)
    (dFiniteNative C hPC F))
theorem e_finite_volume_gamma : RVMapGamma (F.eFinite hc C hPC).obj.volume P :=
  canonical_gamma_object_volume_graph hc (FiniteRV.gammaPullbackAt hPC F.eTarget (F.eGamma.target P F.eSpecial.chain)
    (eFiniteNative C hPC F))

def commonProduct : RVFiniteObject (M := M) (C.base : Set M) 2 :=
  rvFiniteProductObject (F.dFinite hc C hPC) (F.eFinite hc C hPC)

def headRawRVIso : canonicalRVObject hc F.headContraction.contractionObject ≅ (F.commonProduct hc C hPC).obj :=
  (fixedNativeRectangleRawRVIso D E z hz hc F.dFixed.special F.dFixed.pullback F.headTail).trans
    ((finiteVolumeProperty (C.base : Set M) 2).ι.mapIso (finiteRVProductIso (F.dLabelIso hc C hPC) (Iso.refl (F.eFinite hc C hPC))))

def tailRawRVIso : canonicalRVObject hc F.tailContraction.contractionObject ≅ (F.commonProduct hc C hPC).obj :=
  (swappedFixedNativeRectangleRawRVIso D E z hz hc F.eFixed.special F.eFixed.pullback F.tailTail).trans
    ((finiteVolumeProperty (C.base : Set M) 2).ι.mapIso (finiteRVProductIso (Iso.refl (F.dFinite hc C hPC)) (F.eLabelIso hc C hPC)))

theorem head_raw_coordinates : ∀ u, (F.commonProduct hc C hPC).obj.value ((F.headRawRVIso hc C hPC).hom.map u) =
    (canonicalRVObject hc F.headContraction.contractionObject).value u := by
  intro u
  calc
    _ = (rvFiniteProductObject (F.dFixedFinite hc C hPC) (F.eFinite hc C hPC)).obj.value
        ((fixedNativeRectangleRawRVIso D E z hz hc F.dFixed.special F.dFixed.pullback F.headTail).hom.map u) :=
      finite_rv_product_iso_value (F.dLabelIso hc C hPC) (Iso.refl (F.eFinite hc C hPC))
        (F.d_label_iso_value hc C hPC) (fun _ => rfl) _
    _ = _ := fixed_native_rectangle_raw_product_map_volume D E z hz hc F.dFixed.special F.dFixed.pullback F.headTail u

theorem tail_raw_coordinates : ∀ u, (F.commonProduct hc C hPC).obj.value ((F.tailRawRVIso hc C hPC).hom.map u) =
    (canonicalRVObject hc F.tailContraction.contractionObject).value u := by
  intro u
  calc
    _ = (rvFiniteProductObject (F.dFinite hc C hPC) (F.eFixedFinite hc C hPC)).obj.value
        ((swappedFixedNativeRectangleRawRVIso D E z hz hc F.eFixed.special F.eFixed.pullback F.tailTail).hom.map u) :=
      finite_rv_product_iso_value (Iso.refl (F.dFinite hc C hPC)) (F.eLabelIso hc C hPC)
        (fun _ => rfl) (F.e_label_iso_value hc C hPC) _
    _ = _ := swapped_fixed_native_rectangle_raw_product_map_volume D E z hz hc F.eFixed.special F.eFixed.pullback F.tailTail u

theorem head_raw_iso_gamma : RVMapGamma (F.headRawRVIso hc C hPC).hom.map P := by
  have hEId : RVMapGamma (finiteIsoMap (Iso.refl (F.eFinite hc C hPC))) P :=
    RVMapGamma.identity hc (F.e_finite_volume_gamma hc C hPC).domain
  exact (fixed_native_rectangle_raw_product_map_gamma D E z hz hc F.dFixed.special F.dFixed.pullback F.headTail).comp
    (finite_rv_product_iso_gamma (F.dLabelIso hc C hPC) (Iso.refl (F.eFinite hc C hPC)) (F.d_label_iso_gamma hc C hPC) hEId)

theorem tail_raw_iso_gamma : RVMapGamma (F.tailRawRVIso hc C hPC).hom.map P := by
  have hDId : RVMapGamma (finiteIsoMap (Iso.refl (F.dFinite hc C hPC))) P :=
    RVMapGamma.identity hc (F.d_finite_volume_gamma hc C hPC).domain
  exact (swapped_fixed_native_rectangle_raw_product_map_gamma D E z hz hc F.eFixed.special F.eFixed.pullback F.tailTail).comp
    (finite_rv_product_iso_gamma (Iso.refl (F.dFinite hc C hPC)) (F.eLabelIso hc C hPC) hDId (F.e_label_iso_gamma hc C hPC))

end IntegrationInACVF.Section7.TwoOrderRectanglePreparations
