import Integration7.VolumeGammaWeightMaps
import Integration7.FiniteImageVolumeExceptions
import Integration7.FiniteVolumeCertificateCriterion

/-! Finite volume certificates whose exception lives on coordinate-and-
density labels. Their existence follows by imaging the original exception;
pullback through the actual finite weight map proves the converse. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def volumeIsoChartAt {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (A : Finset (VolumeChartSupport (k+1)))
    (u : U.essential.obj.domain) : Prop :=
  ∃ σ ∈ A, VolumeChartValue σ (volumeCorrespondence (finiteIsoMap e)).carrier
    (productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)))
    (fun _ => volumeRatio U V e u)

theorem volumeIsoChartAt_isRVJacobianAt {U V : PositiveRVVolumeObject (M := M) S k}
    {e : U.essential ≅ V.essential} {A : Finset (VolumeChartSupport (k+1))}
    {u : U.essential.obj.domain} (h : volumeIsoChartAt e A u) :
    IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
      (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) (volumeRatio U V e u) := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  obtain ⟨σ,_,h⟩ := h
  have hj := h.isRVJacobianAt
  have hl : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) ∘
      productLeft (k+1) (k+1) = U.essential.obj.value u := funext (productTuple_left _ _)
  have hr : productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)) ∘
      productRight (k+1) (k+1) = V.essential.obj.value (finiteIsoMap e u) :=
    funext (productTuple_right _ _)
  simpa only [hl,hr] using hj

theorem RVVolumeIso.exists_weight_label_charts
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    ∃ (A : Finset (VolumeChartSupport (k+1)))
      (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) (C.base : Set M)),
      rvDim D < k+1 ∧ ∀ u, volumeGammaWeightTuple U u ∉ D.carrier → volumeIsoChartAt e.iso A u := by
  obtain ⟨A,hA⟩ := e.exists_finite_volume_charts hc C
  obtain ⟨D,_,hd,hD⟩ := RVAlmostEverywhere.pushforward_all hc C (volumeGammaWeightMap U) hA
  refine ⟨A,D,hd,?_⟩
  intro u hu
  have hnot : (volumeGammaWeightMap U u).val ∉ D.carrier := by
    rwa [volumeGammaWeightMap_value]
  exact hD _ hnot u rfl

theorem RVVolumeIso.exists_bounded_weight_label_certificate
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) :
    ∃ (A : Finset (VolumeChartSupport (k+1)))
      (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) (C.base : Set M)) (j : ℕ), j < k+1 ∧
      ∃ (g : Map D (DefSet.univ (rawRVSpace (M := M) j) (C.base : Set M))) (N : ℕ),
        g.FiniteFibres ∧
        (∀ y : Fin j → M, (∀ i, iRV (y i)) →
          {x : Fin ((k+1)+1) → M | (y,x) ∈ rawRVMapReverseGraph g}.ncard ≤ N) ∧
        ∀ u, volumeGammaWeightTuple U u ∉ D.carrier → volumeIsoChartAt e.iso A u := by
  obtain ⟨A,D,hd,hA⟩ := e.exists_weight_label_charts hc C
  obtain ⟨g,hg⟩ := rvDim_attained D
  obtain ⟨N,hN⟩ := finiteRVMap_uniform_bound hc C.uncountable.le C.saturated C.small g hg
  exact ⟨A,D,rvDim D,hd,g,N,hg,hN,hA⟩

def rvVolumeIsoOfWeightLabelCharts {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (A : Finset (VolumeChartSupport (k+1)))
    (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) S) (hd : rvDim D < k+1)
    (hΓ : ∀ u, essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u))
    (hA : ∀ u, volumeGammaWeightTuple U u ∉ D.carrier → volumeIsoChartAt e A u) : RVVolumeIso U V := by
  let B := DefSet.univ (rawRVSpace (M := M) ((k+1)+1)) S
  have hTarget : RVAlmostEverywhere B (k+1) (fun w => ∀ u, volumeGammaWeightMap U u = w →
      volumeIsoChartAt e A u) := by
    refine ⟨D,Set.subset_univ _,hd,?_⟩
    intro w hw u he
    apply hA u
    intro hmem
    apply hw
    have heval := congrArg (fun z : B => z.val) he
    rw [volumeGammaWeightMap_value] at heval
    exact heval ▸ hmem
  have hPull := RVAlmostEverywhere.pullback_finite (volumeGammaWeightMap U) (volumeGammaWeightMap_finite U) hTarget
  refine ⟨e,fun u => gammaVolumeEquation_of_weight e u (hΓ u),?_⟩
  exact hPull.mono (fun u h => volumeIsoChartAt_isRVJacobianAt (h u rfl))

end IntegrationInACVF.Section7
