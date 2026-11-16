module

public import Integration7.HeadCoordinateFibreVolumeSelectors
public import Integration7.HeadFibreRawVolumePresentation
public import Integration7.GammaEqualLabelEquivalenceGraphs
public import IntegrationSection6.RawFiniteContractions
public import IntegrationSection6.RawContractionDomain

@[expose] public section

/-! A first head contraction with no old selected coordinates is the
raw finite unary contraction of its actual frozen fibre. The full label
identity preserves its sole volume coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

theorem head_coordinate_fibre_finite_labels
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (x : Fin n → VF (M := M)) (y : Fin 1 → VF (M := M)) :
    {r : Fin a → RV (M := M) | (y,r) ∈ carrier (coordinateFibre U 0 (headFrozenTuple x))}.Finite :=
  hfin (Function.update (headFrozenTuple x) 0 (y 0))

set_option maxHeartbeats 1600000 in
theorem head_finite_raw_volume_equivalence {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x) :
    let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
    let hBR : Bx.real ⊆ coordinateFibreBase S 0 (headFrozenTuple x) := by
      rw [head_coordinate_fibre_base];exact Set.union_subset_union hBS (Set.Subset.refl _)
    let TX := headCoordinateFibreContraction T x
    let Z := FiniteRV.gammaRawFiniteContraction hκ hs
      (small_union_range hκ B.real hreal (fun j => (x j).val)) hBR (gamma_head_fibre U hU x)
      (head_coordinate_fibre_finite_labels hfin x) TX (gamma_head_coordinate_fibre_contraction T hT hTarget x)
    ∃ e : GammaRVIso P.toGamma.toGammaRVObject Z.toGammaRVObject,
      (∀ u, gammaVolumeValue Z.toGammaRVObject (e.equiv u) = gammaVolumeValue P.toGamma.toGammaRVObject u) ∧
      (∀ u, (e.equiv u).val = u.val) := by
  intro Bx hBR TX Z
  have hDom (r : Fin (1+T.arity) → RV (M := M)) :
      r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ _ P.domain ↔
      r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ _ (rvObjectDomain Z.object) :=
    (Set.ext_iff.mp P.domain_eq r).trans
      ((head_coordinate_fibre_contraction_domain T x r).symm.trans (rawContractionDomain_iff TX (Fin.elim0,r)).symm)
  let e : P.domain ≃ rvObjectDomain Z.object := {
    toFun := fun u => ⟨u.val,(hDom u.val).mp u.property⟩
    invFun := fun v => ⟨v.val,(hDom v.val).mpr v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcoord (u : P.domain) : gammaVolumeValue Z.toGammaRVObject (e u) = gammaVolumeValue P.toGamma.toGammaRVObject u := by
    have hP := (P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩
    change u.val ∘ TX.volumeIndex = (P.volume u).val
    rw [← hP.2.2]
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change u.val ((headCoordinateFibreContraction T x).volumeIndex 0) =
      u.val (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a) 0)
    rw [head_coordinate_fibre_volume_index T x]
    rfl
  let f := FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Z e
    (gamma_equal_label_equivalence_graph _ _ P.toGamma.domain_graph e (fun _ => rfl))
    (fun u => congrArg (fun t : Fin 1 → RV (M := M) => rawWeight (rvValues t)) (hcoord u).symm)
  exact ⟨f,hcoord,fun _ => rfl⟩

end IntegrationInACVF.Section7
