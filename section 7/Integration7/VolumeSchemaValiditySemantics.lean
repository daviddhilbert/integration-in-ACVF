import Integration7.VolumeSchemaRowSemantics
import Integration7.WeightLabelVolumeCertificates

/-! The first-order Gamma and RV validity clauses imply the actual two
volume equations on an interpreted essential bijection. The finite
exception map supplies the required strict RV-dimension bound. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k j : ℕ} {sp : Fin p → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}
variable {H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M)}

theorem RVVolumeSchemaRow.gammaWeight (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (hH : ∀ u : U.essential.obj.domain,
      Fin.append (Fin.append z (rvValues u.val)) (rvValues (finiteIsoMap e u).val) ∈ H)
    (hΓ : volumeChartGammaRowValid F G H z) (u : U.essential.obj.domain) :
    essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u) := by
  apply (volumeGammaWeightTuple_balance_iff U V u (finiteIsoMap e u)).mp
  exact volumeChartGammaRowValid_apply F G H z hΓ _ _
    (fun i => (volumeGammaWeightTuple U u i).property)
    (fun i => (volumeGammaWeightTuple V (finiteIsoMap e u) i).property)
    _ _ (P.weighted_at u) (hH u) (Q.weighted_at (finiteIsoMap e u))

theorem RVVolumeSchemaRow.chartAt (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (A : Finset (VolumeChartSupport (k+1))) (E : GammaFiniteRVSchema B p ((k+1)+1) j sp)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (hRV : volumeChartRVRowValid F G H A E z) (u : U.essential.obj.domain)
    (hu : Fin.append z (rvValues (volumeGammaWeightTuple U u)) ∉ E.domain) :
    volumeIsoChartAt e A u := by
  let v := finiteIsoMap e u
  let φ := U.essentialForm.value u
  let ψ := V.essentialForm.value v
  let w := weightedPairTuple z (rvValues (U.essential.obj.value u)) (rvValues (V.essential.obj.value v))
    (fun _ : Fin 1 => φ.val) (fun _ : Fin 1 => ψ.val)
  have hw : w = Fin.append z (Fin.append (rvValues (volumeGammaWeightTuple U u))
      (rvValues (volumeGammaWeightTuple V v))) := by
    rw [volumeGammaWeightTuple_raw_append,volumeGammaWeightTuple_raw_append]
    rfl
  have hOutside : w ∈ weightedPairsOutsideException F G H E := by
    constructor
    · rw [hw]
      exact (schemaVolumeCorrespondence_append (weightedVolumeSchema F) (weightedVolumeSchema G) H z
        _ _ hRV.1 (fun i => (volumeGammaWeightTuple U u i).property)
        (fun i => (volumeGammaWeightTuple V v i).property)).mpr
        ⟨rvValues u.val,rvValues v.val,P.weighted_at u,(hH _ _).mpr ⟨u,rfl,rfl⟩,Q.weighted_at v⟩
    · change w ∘ weightedPairSourceIndices p (k+1) ∉ E.domain
      rw [weightedPairTuple_source]
      exact (volumeGammaWeightTuple_raw_append u) ▸ hu
  have hW : w ∈ supportedSchemaJacobianFormula F G H A := by
    rw [hw]
    apply hRV.2
    rwa [← hw]
  have hJ := (supportedSchemaJacobianFormula_typed_iff F G H A z
    (U.essential.obj.value u) (V.essential.obj.value v) φ ψ hRV.1
    (U.essentialForm_nonzero u) (V.essentialForm_nonzero v)).mp hW
  rw [P.correspondence_eq Q e H hRV.1 hH] at hJ
  exact hJ

def rvVolumeIsoOfValidSchemaRows (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (A : Finset (VolumeChartSupport (k+1))) (E : GammaFiniteRVSchema B p ((k+1)+1) j sp)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (hΓ : volumeChartGammaRowValid F G H z) (hRV : volumeChartRVRowValid F G H A E z)
    (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) S)
    (hD : ∀ w, w ∈ D.carrier ↔ Fin.append z (rvValues w) ∈ E.domain)
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) S)) (hg : g.FiniteFibres)
    (hj : j < k+1) : RVVolumeIso U V := by
  have hd : rvDim D < k+1 :=
    ((rvDim_le_of_finite_map g hg).trans (rvDim_le_arity _)).trans_lt hj
  apply rvVolumeIsoOfWeightLabelCharts e A D hd
  · intro u
    exact P.gammaWeight Q e (fun u => (hH _ _).mpr ⟨u,rfl,rfl⟩) hΓ u
  · intro u hu
    exact P.chartAt Q e A E hH hRV u (fun h => hu ((hD _).mpr h))

@[simp] theorem rvVolumeIsoOfValidSchemaRows_underlying
    (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (A : Finset (VolumeChartSupport (k+1))) (E : GammaFiniteRVSchema B p ((k+1)+1) j sp)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (hΓ : volumeChartGammaRowValid F G H z) (hRV : volumeChartRVRowValid F G H A E z)
    (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) S)
    (hD : ∀ w, w ∈ D.carrier ↔ Fin.append z (rvValues w) ∈ E.domain)
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) S)) (hg : g.FiniteFibres) (hj : j < k+1) :
    (rvVolumeIsoOfValidSchemaRows P Q e A E hH hΓ hRV D hD g hg hj).iso = e := rfl

end IntegrationInACVF.Section7
