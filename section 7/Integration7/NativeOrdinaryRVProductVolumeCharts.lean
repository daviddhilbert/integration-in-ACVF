import Integration7.NativeOrdinaryRVVolumeFactors
import Integration7.NativeRVProductMapTransfers
import Integration7.VolumeProductPointwise
import Integration7.ZeroFactorVolumeObjects
import Integration7.VolumeRelabeling
import IntegrationSection6.FiniteBlowups

/-! A genuine native product bijection with a finite ordinary factor
constructs a full volume chart without adding any volume coordinate or
density for that degree-zero factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {l d r k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r)
variable (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
variable (hf : Function.Bijective f) (κ : Fin r → Fin l) (hκ : ∀ q : Q, (f q).val.2.2=q.val.2 ∘ κ)
variable (hR : (rawVolumeContractionLabels hc R).carrier.Finite)
variable (τ : Fin (k+1) → Fin r) (ε : Fin r)
variable (hZ : ∀ t : Fin (k+1) → RV (M := M),
  {s : Fin r → RV (M := M) | (Fin.elim0,s) ∈ carrier Z ∧ s ∘ τ=t}.Finite)
variable (hε : ∀ q : Z, (q.val.2 ε).val ≠ iRVZero)

private def coordinates : RVObject (M := M) (C.base : Set M) (k+1) where
  arity := l
  domain := rawVolumeContractionLabels hc Q
  volume := (rvCoordinateSelectMap (C.base : Set M) (κ ∘ τ)).restrict (Set.subset_univ _)
private def targetObject := PositiveRVVolumeObject.zero_prod (nativeOrdinaryRVObject hc C R hR)
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
    (targetObject hc C R Z hR τ ε hZ hε).underlying.obj.value (nativeRVProductMapTransfer hc f u) =
      (coordinates hc C Q κ τ).value u := by
  exact (zeroPositiveProduct_coordinates (nativeOrdinaryRVObject hc C R hR)
    (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε) (nativeRVProductMapTransfer hc f u)).trans (by
      change (rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.2 ∘ τ = _
      rw [right_labels hc C Q R Z f κ hκ u]
      rfl)

private def coordinateIso : coordinates hc C Q κ τ ≅ (targetObject hc C R Z hR τ ε hZ hε).underlying.obj :=
  rvIsoOfVolumePreservingBijection (nativeRVProductMapTransfer hc f)
    (native_rv_product_map_transfer_bijective hc f hf)
    (coordinate_value hc C Q R Z f κ hκ hR τ ε hZ hε)

def nativeOrdinaryRVProductVolumeChart : PositiveRVVolumeObject (M := M) (C.base : Set M) k where
  underlying := ⟨coordinates hc C Q κ τ,
    (finite_volume_iso (coordinateIso hc C Q R Z f hf κ hκ hR τ ε hZ hε)).mpr
      (targetObject hc C R Z hR τ ε hZ hε).underlying.property⟩
  form := (targetObject hc C R Z hR τ ε hZ hε).form.pullback (nativeRVProductMapTransfer hc f)

def nativeOrdinaryRVProductVolumeChartIso :
    RVVolumeIso (nativeOrdinaryRVProductVolumeChart hc C Q R Z f hf κ hκ hR τ ε hZ hε)
      (PositiveRVVolumeObject.zero_prod (nativeOrdinaryRVObject hc C R hR)
        (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε)) :=
  RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (coordinateIso hc C Q R Z f hf κ hκ hR τ ε hZ hε))
    (coordinate_value hc C Q R Z f κ hκ hR τ ε hZ hε) (fun _ => rfl)

theorem native_ordinary_rv_product_volume_chart_density
    (u : (nativeOrdinaryRVProductVolumeChart hc C Q R Z f hf κ hκ hR τ ε hZ hε).underlying.obj.domain) :
    (nativeOrdinaryRVProductVolumeChart hc C Q R Z f hf κ hκ hR τ ε hZ hε).form.value u = u.val (κ ε) := by
  change (rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.2 ε = _
  exact congrFun (right_labels hc C Q R Z f κ hκ u) ε
end IntegrationInACVF.Section7
