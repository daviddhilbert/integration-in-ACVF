module

public import Integration7.FixedNativeRectangleContractions
public import Integration7.NativeUnaryRectangleRawIsomorphisms
public import Section4.RVProductSymmetry

@[expose] public section

/-! The two constructed standard contractions of the same fixed-label
rectangle compare to unary products in the original VF coordinate order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (SpecialBijection IsRVPullback headImage pullbackObject)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d r b : ℕ}
variable (D E : SpecialTransformations.Section5.DefSet (M := M) S 1 0)
variable (z : Fin d → SpecialTransformations.Section5.RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
variable {D' : SpecialTransformations.Section5.DefSet (M := M) S 1 r}
variable {E' : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
variable (hc : CanonicalStructure.IsCanonical (M := M))

def fixedNativeRectangleRawProductMap (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (SpecialTransformations.Section5.carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    Map (canonicalRVObject hc (fixedNativeRectangleContraction D E z hz T hD L).contractionObject).domain
      (rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E'))).domain :=
  nativeRectangleRawProductMap hc T hD L

theorem fixed_native_rectangle_raw_product_map_bijective (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (SpecialTransformations.Section5.carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    Function.Bijective (fixedNativeRectangleRawProductMap D E z hz hc T hD L) :=
  native_rectangle_raw_product_map_bijective hc T hD L

theorem fixed_native_rectangle_raw_product_map_volume (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (SpecialTransformations.Section5.carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P)
    (p : (canonicalRVObject hc (fixedNativeRectangleContraction D E z hz T hD L).contractionObject).domain) :
    (rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E'))).value
      (fixedNativeRectangleRawProductMap D E z hz hc T hD L p) =
      (canonicalRVObject hc (fixedNativeRectangleContraction D E z hz T hD L).contractionObject).value p := by
  have h := native_rectangle_raw_product_map_volume hc T hD L p
  funext i
  have hi := congrFun h i
  change _ = p.val ((fixedNativeRectangleContraction D E z hz T hD L).volumeIndex i)
  rw [fixed_native_rectangle_volume_index]
  change _ = p.val ((nativeUnaryRectangleContraction T hD L).volumeIndex i) at hi
  rw [native_rectangle_standard_volume_index] at hi
  exact hi

def fixedNativeRectangleRawRVIso (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (SpecialTransformations.Section5.carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    canonicalRVObject hc (fixedNativeRectangleContraction D E z hz T hD L).contractionObject ≅
      rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E')) :=
  rvIsoOfVolumePreservingBijection (fixedNativeRectangleRawProductMap D E z hz hc T hD L)
    (fixed_native_rectangle_raw_product_map_bijective D E z hz hc T hD L)
    (fixed_native_rectangle_raw_product_map_volume D E z hz hc T hD L)

theorem fixed_native_rectangle_raw_product_map_gamma (T : SpecialBijection (fixedRVLabelDomain D z hz) D')
    (hD : IsRVPullback (SpecialTransformations.Section5.carrier D')) {W : SpecialBijection E E'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D' E)) (headImage D') P) :
    RVMapGamma (fixedNativeRectangleRawProductMap D E z hz hc T hD L) P := native_rectangle_raw_product_map_gamma hc T hD L

omit D E z hz hc in
theorem unary_rv_product_swap_volume (U V : RVObject (M := M) S 1) (p : (rvProductObject U V).domain) :
    (rvProductObject V U).value (rvProductSwapMap U V p) = (rvProductObject U V).value p ∘ Equiv.swap 0 1 := by
  rw [rvProductObject_value,rvProductSwapMap_unpack,rvProductObject_value]
  funext i
  fin_cases i <;> rfl

def swappedFixedNativeRectangleRawProductMap (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    Map (canonicalRVObject hc (swappedFixedNativeRectangleContraction D E z hz T hE L).contractionObject).domain
      (rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E'))).domain :=
  Map.comp (rvProductSwapMap (canonicalRVObject hc (pullbackObject E')) (canonicalRVObject hc (pullbackObject D')))
    (nativeRectangleRawProductMap hc T hE L)

theorem swapped_fixed_native_rectangle_raw_product_map_bijective (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    Function.Bijective (swappedFixedNativeRectangleRawProductMap D E z hz hc T hE L) :=
  (rvProductSwapMap_bijective _ _).comp (native_rectangle_raw_product_map_bijective hc T hE L)

theorem swapped_fixed_native_rectangle_raw_product_map_volume (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P)
    (p : (canonicalRVObject hc (swappedFixedNativeRectangleContraction D E z hz T hE L).contractionObject).domain) :
    (rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E'))).value
      (swappedFixedNativeRectangleRawProductMap D E z hz hc T hE L p) =
      (canonicalRVObject hc (swappedFixedNativeRectangleContraction D E z hz T hE L).contractionObject).value p := by
  have hSwap := unary_rv_product_swap_volume (canonicalRVObject hc (pullbackObject E'))
    (canonicalRVObject hc (pullbackObject D')) (nativeRectangleRawProductMap hc T hE L p)
  have hNative := native_rectangle_raw_product_map_volume hc T hE L p
  have h := hSwap.trans (congrArg (fun v => v ∘ Equiv.swap 0 1) hNative)
  funext i
  have hi := congrFun h i
  change _ = p.val ((swappedFixedNativeRectangleContraction D E z hz T hE L).volumeIndex i)
  rw [swapped_fixed_native_rectangle_volume_index]
  change _ = p.val ((nativeUnaryRectangleContraction T hE L).volumeIndex ((Equiv.swap 0 1) i)) at hi
  rw [native_rectangle_standard_volume_index] at hi
  exact hi

def swappedFixedNativeRectangleRawRVIso (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    canonicalRVObject hc (swappedFixedNativeRectangleContraction D E z hz T hE L).contractionObject ≅
      rvProductObject (canonicalRVObject hc (pullbackObject D')) (canonicalRVObject hc (pullbackObject E')) :=
  rvIsoOfVolumePreservingBijection (swappedFixedNativeRectangleRawProductMap D E z hz hc T hE L)
    (swapped_fixed_native_rectangle_raw_product_map_bijective D E z hz hc T hE L)
    (swapped_fixed_native_rectangle_raw_product_map_volume D E z hz hc T hE L)

theorem swapped_fixed_native_rectangle_raw_product_map_value (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P)
    (p : (canonicalRVObject hc (swappedFixedNativeRectangleContraction D E z hz T hE L).contractionObject).domain) :
    (swappedFixedNativeRectangleRawProductMap D E z hz hc T hE L p).val =
      Fin.append (p.val ∘ L.headProjection) (p.val ∘ L.headParameters) := by
  have h := native_rectangle_raw_product_map_unpack hc T hE L p
  change Fin.append
    (rvUnpack (canonicalRVObject hc (pullbackObject E')).domain (canonicalRVObject hc (pullbackObject D')).domain
      (nativeRectangleRawProductMap hc T hE L p)).val.2
    (rvUnpack (canonicalRVObject hc (pullbackObject E')).domain (canonicalRVObject hc (pullbackObject D')).domain
      (nativeRectangleRawProductMap hc T hE L p)).val.1 = _
  rw [h]

theorem swapped_fixed_native_rectangle_raw_product_map_gamma (T : SpecialBijection (fixedRVLabelDomain E z hz) E')
    (hE : IsRVPullback (SpecialTransformations.Section5.carrier E')) {W : SpecialBijection D D'}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain E' D)) (headImage E') P) :
    RVMapGamma (swappedFixedNativeRectangleRawProductMap D E z hz hc T hE L) P := by
  apply gamma_real_rv_map_graph hc P _
    (rvCoordinateSelectMap P.real (Fin.append L.headProjection L.headParameters))
    (L.canonical_raw_head_product_map_gamma hc).domain
  intro u
  have h := swapped_fixed_native_rectangle_raw_product_map_value D E z hz hc T hE L u
  exact h.trans (by
    change Fin.append (u.val ∘ L.headProjection) (u.val ∘ L.headParameters) =
      u.val ∘ Fin.append L.headProjection L.headParameters
    funext j
    cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right])

end IntegrationInACVF.Section7
