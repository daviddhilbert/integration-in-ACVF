module

public import Integration7.HKNativeZeroDensityObjects
public import Integration7.HKRVVolumeProducts
public import Integration7.NativeRVProductMapTransfers
public import Integration7.VolumeProductPointwise
public import Integration7.ZeroFactorVolumeObjects
public import Integration7.VolumeRelabeling
public import IntegrationSection6.FiniteBlowups

@[expose] public section

/-! A genuine finite weighted factor and a positive prepared head give
a full coordinate-density product chart. Both original forms survive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {l d r k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r)
variable (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
variable (hf : Function.Bijective f) (κ : Fin r → Fin l) (hκ : ∀ q : Q, (f q).val.2.2=q.val.2 ∘ κ)
variable (δ : Fin d) (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
variable (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
variable (τ : Fin (k+1) → Fin r) (ε : Fin r)
variable (hZ : ∀ t : Fin (k+1) → RV (M := M),
  {s : Fin r → RV (M := M) | (Fin.elim0,s) ∈ carrier Z ∧ s ∘ τ=t}.Finite)
variable (hε : ∀ q : Z, (q.val.2 ε).val ≠ iRVZero)

private def coordinates : RVObject (M := M) (C.base : Set M) (k+1) where
  arity := l
  domain := rawVolumeContractionLabels hc Q
  volume := (rvCoordinateSelectMap (C.base : Set M) (κ ∘ τ)).restrict (Set.subset_univ _)
private def targetObject := zeroProduct (nativeZeroDensityObject hc C R δ hR hδ)
  (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε)

include hκ in
private theorem right_labels (u : rawVolumeContractionLabels hc Q) :
    (rvUnpack (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)
      (nativeRVProductMapTransfer hc f u)).val.2=u.val ∘ κ := by
  let q : Q := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc Q u.val).mp u.property⟩
  let w := rvUnpack (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z) (nativeRVProductMapTransfer hc f u)
  have h := congrArg Subtype.val (rvPack_unpack (rawVolumeContractionLabels hc R)
    (rawVolumeContractionLabels hc Z) (nativeRVProductMapTransfer hc f u))
  change Fin.append w.val.1 w.val.2=(nativeRVProductMapTransfer hc f u).val at h
  rw [native_rv_product_map_transfer_value] at h
  change Fin.append w.val.1 w.val.2=Fin.append (f q).val.1.2 (f q).val.2.2 at h
  rw [hκ] at h
  funext i
  simpa only [Fin.append_right] using congrFun h (Fin.natAdd d i)

include hκ in
private theorem coordinate_value (u : rawVolumeContractionLabels hc Q) :
    (targetObject hc C R Z δ hR hδ τ ε hZ hε).underlying.obj.value (nativeRVProductMapTransfer hc f u) =
      (coordinates hc C Q κ τ).value u := by
  exact (zeroProduct_coordinates (nativeZeroDensityObject hc C R δ hR hδ)
    (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε) (nativeRVProductMapTransfer hc f u)).trans (by
      change (rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.2 ∘ τ = _
      rw [right_labels hc C Q R Z f κ hκ u]
      rfl)

private def coordinateIso : coordinates hc C Q κ τ ≅ (targetObject hc C R Z δ hR hδ τ ε hZ hε).underlying.obj :=
  rvIsoOfVolumePreservingBijection (nativeRVProductMapTransfer hc f)
    (native_rv_product_map_transfer_bijective hc f hf)
    (coordinate_value hc C Q R Z f κ hκ δ hR hδ τ ε hZ hε)

def nativeZeroRVProductVolumeChart : PositiveRVVolumeObject (M := M) (C.base : Set M) k where
  underlying := ⟨coordinates hc C Q κ τ,
    (finite_volume_iso (coordinateIso hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε)).mpr
      (targetObject hc C R Z δ hR hδ τ ε hZ hε).underlying.property⟩
  form := (targetObject hc C R Z δ hR hδ τ ε hZ hε).form.pullback (nativeRVProductMapTransfer hc f)

def nativeZeroRVProductVolumeChartIso :
    RVVolumeIso (nativeZeroRVProductVolumeChart hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε)
      (zeroProduct (nativeZeroDensityObject hc C R δ hR hδ)
        (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε)) :=
  RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (coordinateIso hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε))
    (coordinate_value hc C Q R Z f κ hκ δ hR hδ τ ε hZ hε) (fun _ => rfl)

theorem native_zero_rv_product_volume_chart_density
    (ι : Fin d → Fin l) (hι : ∀ q : Q, (f q).val.1.2=q.val.2 ∘ ι)
    (u : (nativeZeroRVProductVolumeChart hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε).underlying.obj.domain) :
    (nativeZeroRVProductVolumeChart hc C Q R Z f hf κ hκ δ hR hδ τ ε hZ hε).form.value u =
      u.val (ι δ) * u.val (κ ε) := by
  let w := rvUnpack (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)
    (nativeRVProductMapTransfer hc f u)
  have hLeft : w.val.1 = u.val ∘ ι := by
    let q : Q := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc Q u.val).mp u.property⟩
    have h := congrArg Subtype.val (rvPack_unpack (rawVolumeContractionLabels hc R)
      (rawVolumeContractionLabels hc Z) (nativeRVProductMapTransfer hc f u))
    change Fin.append w.val.1 w.val.2=(nativeRVProductMapTransfer hc f u).val at h
    rw [native_rv_product_map_transfer_value] at h
    change Fin.append w.val.1 w.val.2=Fin.append (f q).val.1.2 (f q).val.2.2 at h
    rw [hι] at h
    funext j
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd r j)
  change w.val.1 δ * w.val.2 ε = _
  rw [hLeft,right_labels hc C Q R Z f κ hκ u]
  rfl
end IntegrationInACVF.Section7.HK
