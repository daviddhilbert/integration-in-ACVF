module

public import Integration7.NativeRVProductMapTransfers
public import Integration7.NativeCoordinateDensityVolumeObjects
public import Integration7.VolumeProductPointwise
public import Integration7.VolumeRelabeling
public import IntegrationSection6.FiniteBlowups

@[expose] public section

/-! A genuine native product bijection with literal label projections
constructs a finite coordinate-density volume chart on its original
source. Functional extra labels remain in that source domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier RV)
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {l d r p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r)
variable (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
variable (hf : Function.Bijective f) (ι : Fin d → Fin l) (κ : Fin r → Fin l)
variable (hι : ∀ q : Q, (f q).val.1.2=q.val.2 ∘ ι) (hκ : ∀ q : Q, (f q).val.2.2=q.val.2 ∘ κ)
variable (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin r) (δ : Fin d) (ε : Fin r)
variable (hR : ∀ t : Fin (p+1) → RV (M := M), {s : Fin d → RV (M := M) | (Fin.elim0,s) ∈ carrier R ∧ s ∘ σ=t}.Finite)
variable (hZ : ∀ t : Fin (k+1) → RV (M := M), {s : Fin r → RV (M := M) | (Fin.elim0,s) ∈ carrier Z ∧ s ∘ τ=t}.Finite)
variable (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero) (hε : ∀ q : Z, (q.val.2 ε).val ≠ iRVZero)

private def sourceCoordinates : RVObject (M := M) (C.base : Set M) (((p+1)+k)+1) where
  arity := l
  domain := rawVolumeContractionLabels hc Q
  volume := (rvCoordinateSelectMap (C.base : Set M) (Fin.append (ι ∘ σ) (κ ∘ τ))).restrict (Set.subset_univ _)

private def leftFactor := nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ
private def rightFactor := nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε

include hι hκ in
private theorem factor_labels (u : rawVolumeContractionLabels hc Q) :
    let w := rvUnpack (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)
      (nativeRVProductMapTransfer hc f u)
    w.val.1=u.val ∘ ι ∧ w.val.2=u.val ∘ κ := by
  intro w
  let q : Q := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc Q u.val).mp u.property⟩
  have h := congrArg Subtype.val (rvPack_unpack (rawVolumeContractionLabels hc R)
    (rawVolumeContractionLabels hc Z) (nativeRVProductMapTransfer hc f u))
  change Fin.append w.val.1 w.val.2=(nativeRVProductMapTransfer hc f u).val at h
  rw [native_rv_product_map_transfer_value] at h
  change Fin.append w.val.1 w.val.2=Fin.append (f q).val.1.2 (f q).val.2.2 at h
  rw [hι,hκ] at h
  constructor
  · funext j
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd r j)
  · funext j
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd d j)

include hι hκ in
private theorem coordinate_value (u : rawVolumeContractionLabels hc Q) :
    ((leftFactor hc C R σ δ hR hδ).prod (rightFactor hc C Z τ ε hZ hε)).underlying.obj.value
      (nativeRVProductMapTransfer hc f u) = (sourceCoordinates hc C Q ι κ σ τ).value u := by
  have h := factor_labels hc C Q R Z f ι κ hι hκ u
  change Fin.append ((rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.1 ∘ σ)
    ((rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.2 ∘ τ)=u.val ∘ Fin.append (ι ∘ σ) (κ ∘ τ)
  rw [h.1,h.2]
  funext j
  cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right]

private def coordinateIso : sourceCoordinates hc C Q ι κ σ τ ≅
    ((leftFactor hc C R σ δ hR hδ).prod (rightFactor hc C Z τ ε hZ hε)).underlying.obj :=
  rvIsoOfVolumePreservingBijection (nativeRVProductMapTransfer hc f)
    (native_rv_product_map_transfer_bijective hc f hf)
    (coordinate_value hc C Q R Z f ι κ hι hκ σ τ δ ε hR hZ hδ hε)

def nativeRVProductVolumeChart : PositiveRVVolumeObject (M := M) (C.base : Set M) ((p+1)+k) where
  underlying := ⟨sourceCoordinates hc C Q ι κ σ τ,
    (finite_volume_iso (coordinateIso hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε)).mpr
      ((leftFactor hc C R σ δ hR hδ).prod (rightFactor hc C Z τ ε hZ hε)).underlying.property⟩
  form := ((leftFactor hc C R σ δ hR hδ).prod (rightFactor hc C Z τ ε hZ hε)).form.pullback
    (nativeRVProductMapTransfer hc f)

def nativeRVProductVolumeChartIso :
    RVVolumeIso (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε)
      ((nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ).prod
        (nativeCoordinateDensityVolumeObject hc C Z τ ε hZ hε)) :=
  RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (coordinateIso hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε))
    (coordinate_value hc C Q R Z f ι κ hι hκ σ τ δ ε hR hZ hδ hε) (fun _ => rfl)

theorem native_rv_product_volume_chart_coordinates
    (u : (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).underlying.obj.domain) :
    (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).underlying.obj.value u =
      u.val ∘ Fin.append (ι ∘ σ) (κ ∘ τ) := rfl

theorem native_rv_product_volume_chart_density
    (u : (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).underlying.obj.domain) :
    (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).form.value u =
      u.val (ι δ) * u.val (κ ε) := by
  have h := factor_labels hc C Q R Z f ι κ hι hκ u
  change (rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.1 δ *
    (rvUnpack _ _ (nativeRVProductMapTransfer hc f u)).val.2 ε = _
  rw [h.1,h.2]
  rfl
end IntegrationInACVF.Section7
