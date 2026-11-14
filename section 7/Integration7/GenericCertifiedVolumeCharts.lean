import Integration7.RVAlmostEverywhereFiniteMaps
import Integration7.FiniteVolumeIsoMaps
import Section9.GenericRVJacobian

/-! Actual finite chart supports cover a volume correspondence generically.
The small exceptional locus follows from the native full-dimension argument;
it is not a hypothesis on the isomorphism being encoded. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
local notation "RV" => CanonicalRV.RVSort M

theorem volumeChartUnion_relationDefinable
    (hc : CanonicalStructure.IsCanonical (M := M))
    (C : DefSet (rawRVSpace (M := M) (n+n)) S) (A : Finset (VolumeChartSupport n)) :
    (rawRVSpace (M := M) (n+n)).RelationDefinable (rawRVSpace (M := M) 1) S
      (fun t ω => ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω) := by
  classical
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  induction A using Finset.induction_on with
  | empty =>
    apply ((P.definable_empty S).left_relation P Q).congr P Q
    simp
  | insert σ A hσ ih =>
    apply ((volumeChartValue_relationDefinable hc σ C).union P Q ih).congr P Q
    simp [Finset.mem_insert,or_and_right,exists_or]

theorem exists_finite_generic_volume_charts
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (B.base : Set M) n} (e : U ≅ V)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ u : V.obj.domain, ∀ i, (V.obj.value u i).val ≠ iRVZero) :
    ∃ A : Finset (VolumeChartSupport n), RVAlmostEverywhere U.obj.domain n (fun u =>
      ∃ ω : Fin 1 → RV, ∃ σ ∈ A,
        VolumeChartValue σ (volumeCorrespondence (U := U.obj) (V := V.obj) (finiteIsoMap e)).carrier
          (productTuple (U.obj.value u) (V.obj.value (finiteIsoMap e u))) ω) := by
  classical
  let E : U.obj ≅ V.obj := (finiteVolumeProperty (B.base : Set M) n).ι.mapIso e
  let C := volumeCorrespondence E.hom.map
  let P := rawRVSpace (M := M) (n+n)
  let Q := rawRVSpace (M := M) 1
  obtain ⟨A,hA⟩ := exists_finite_volume_chart_cover hc B E
  let R (t : P.Carrier) (ω : Q.Carrier) := ∃ σ ∈ A, VolumeChartValue σ C.carrier t ω
  have hR : P.RelationDefinable Q (B.base : Set M) R := volumeChartUnion_relationDefinable hc C A
  let D := C.sdiff ⟨{t | ∃ ω, R t ω},hR.exists_right P Q⟩
  have hD₀ (t) (ht : t ∈ D.carrier) (i : Fin (n+n)) : (t i).val ≠ iRVZero := by
    obtain ⟨u,rfl⟩ := ht.1
    obtain ⟨j | j,rfl⟩ := finSumFinEquiv.surjective i
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productLeft n n j)).val ≠ iRVZero
      rw [productTuple_left]
      exact hU u j
    · change (productTuple (U.obj.value u) (V.obj.value (E.hom.map u)) (productRight n n j)).val ≠ iRVZero
      rw [productTuple_right]
      exact hV (E.hom.map u) j
  have hd : rvDim D < n := by
    by_contra h
    have hh := (volumePair_leftProjection_finite E.hom.map U.property).restrict
      (show D.carrier ⊆ C.carrier from Set.diff_subset)
    have hd' : rvDim D = n := ((rvDim_le_of_finite_map _ hh).trans (rvDim_le_arity _)).antisymm
      (Nat.le_of_not_gt h)
    obtain ⟨p,hp,ω,σ,hσ,hJ⟩ := exists_chartValue_of_full_volumePair_dimension hc B hn
      E U.property A hA D Set.diff_subset hD₀ hd'
    exact hp.2 ⟨ω,σ,hσ,hJ⟩
  have hpair : RVAlmostEverywhere C n (fun t => ∃ ω, R t.val ω) := by
    refine ⟨D,Set.diff_subset,hd,?_⟩
    intro t ht
    by_contra h
    exact ht ⟨t.property,h⟩
  have h := RVAlmostEverywhere.pullback_finite (volumePairMap E.hom.map)
    (volumePairMap_finite E.hom.map U.property) hpair
  refine ⟨A,h.mono ?_⟩
  intro u hu
  change (∃ ω, R ((volumePairMap E.hom.map u).val) ω) at hu
  rw [volumePairMap_apply] at hu
  change (∃ ω, ∃ σ ∈ A, VolumeChartValue σ C.carrier
    (productTuple (U.obj.value u) (V.obj.value (E.hom.map u))) ω)
  exact hu

theorem RVVolumeIso.exists_finite_volume_charts
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : BaseContext M) {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) (B.base : Set M) k} (e : RVVolumeIso U V) :
    ∃ A : Finset (VolumeChartSupport (k+1)),
      RVAlmostEverywhere U.essential.obj.domain (k+1) (fun u => ∃ σ ∈ A,
        VolumeChartValue σ (volumeCorrespondence (finiteIsoMap e.iso)).carrier
          (productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e.iso u)))
          (fun _ => volumeRatio U V e.iso u)) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  obtain ⟨A,hA⟩ := exists_finite_generic_volume_charts hc B (Nat.zero_lt_succ k) e.iso
    U.essential_nonzero V.essential_nonzero
  refine ⟨A,(hA.and hc B e.rv).mono ?_⟩
  rintro u ⟨⟨ω,σ,hσ,hchart⟩,hJ⟩
  have h := hchart.isRVJacobianAt
  have hl : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e.iso u)) ∘
      productLeft (k+1) (k+1) = U.essential.obj.value u := funext (productTuple_left _ _)
  have hr : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e.iso u)) ∘
      productRight (k+1) (k+1) = V.essential.obj.value (finiteIsoMap e.iso u) :=
    funext (productTuple_right _ _)
  rw [hl,hr] at h
  have he : ω = (fun _ => volumeRatio U V e.iso u) := by
    funext i
    fin_cases i
    exact h.unique hJ
  exact ⟨σ,hσ,he ▸ hchart⟩

end IntegrationInACVF.Section7
