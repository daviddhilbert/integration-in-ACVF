import Integration7.GammaVolumeExistentialCertificates
import Integration7.VolumeSchemaValiditySemantics

/-! Soundness of auxiliary exceptional-set certificates. The resulting
volume isomorphism has the fixed original chart; no choice of auxiliary
parameters changes that chart, its coordinate graph or its density. -/

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
variable {S : Set M} {B : Base (M := M)} {p q k j : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}
variable {H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M)}

theorem RVVolumeSchemaRow.extraChartAt (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (A : Finset (VolumeChartSupport (k+1)))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) (y : Fin q → M)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (hRV : extraVolumeChartRVRowValid F G H A E (Fin.append z y))
    (u : U.essential.obj.domain)
    (hu : Fin.append (Fin.append z y) (rvValues (volumeGammaWeightTuple U u)) ∉ E.domain) :
    volumeIsoChartAt e A u := by
  let v := finiteIsoMap e u
  let r := Fin.append (rvValues (volumeGammaWeightTuple U u)) (rvValues (volumeGammaWeightTuple V v))
  have hz (i) : sortEval (sp i) (z i) := by
    simpa only [Fin.append_left] using hRV.1 (Fin.castAdd q i)
  have hsource : Fin.append (Fin.append z y) r ∘ weightedPairSourceIndices (p+q) (k+1) =
      Fin.append (Fin.append z y) (rvValues (volumeGammaWeightTuple U u)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [r,Function.comp_apply,weightedPairSourceIndices,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  have hOutside : Fin.append (Fin.append z y) r ∈ extraWeightedPairsOutsideException F G H E := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [append_dropExtraVolumeParameters]
      exact (schemaVolumeCorrespondence_append (weightedVolumeSchema F) (weightedVolumeSchema G) H z
        _ _ hz (fun i => (volumeGammaWeightTuple U u i).property)
        (fun i => (volumeGammaWeightTuple V v i).property)).mpr
        ⟨rvValues u.val,rvValues v.val,P.weighted_at u,(hH _ _).mpr ⟨u,rfl,rfl⟩,Q.weighted_at v⟩
    · rwa [hsource]
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hRV.1 i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa only [r,Fin.append_right,Fin.append_left,sortEval,iRV,rvValues] using (volumeGammaWeightTuple U u i).property
        · simpa only [r,Fin.append_right,sortEval,iRV,rvValues] using (volumeGammaWeightTuple V v i).property
  have hW := (hRV.2 r hOutside).1
  rw [append_dropExtraVolumeParameters] at hW
  have he : Fin.append z r = weightedPairTuple z (rvValues (U.essential.obj.value u))
      (rvValues (V.essential.obj.value v)) (fun _ : Fin 1 => (U.essentialForm.value u).val)
      (fun _ : Fin 1 => (V.essentialForm.value v).val) := by
    dsimp only [r]
    rw [volumeGammaWeightTuple_raw_append,volumeGammaWeightTuple_raw_append]
    rfl
  rw [he] at hW
  have hJ := (supportedSchemaJacobianFormula_typed_iff F G H A z _ _ _ _ hz
    (U.essentialForm_nonzero u) (V.essentialForm_nonzero v)).mp hW
  rw [P.correspondence_eq Q e H hz hH] at hJ
  exact hJ

def rvVolumeIsoOfExtraSchemaRows (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (A : Finset (VolumeChartSupport (k+1)))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) (y : Fin q → M)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (hΓ : volumeChartGammaRowValid F G H z)
    (hRV : extraVolumeChartRVRowValid F G H A E (Fin.append z y))
    (D : DefSet (rawRVSpace (M := M) ((k+1)+1)) S)
    (hD : ∀ w, w ∈ D.carrier ↔ Fin.append (Fin.append z y) (rvValues w) ∈ E.domain)
    (g : Map D (DefSet.univ (rawRVSpace (M := M) j) S)) (hg : g.FiniteFibres)
    (hj : j < k+1) : RVVolumeIso U V := by
  have hd : rvDim D < k+1 :=
    ((rvDim_le_of_finite_map g hg).trans (rvDim_le_arity _)).trans_lt hj
  apply rvVolumeIsoOfWeightLabelCharts e A D hd
  · intro u
    exact P.gammaWeight Q e (fun u => (hH _ _).mpr ⟨u,rfl,rfl⟩) hΓ u
  · intro u hu
    exact P.extraChartAt Q e A E y hH hRV u (fun h => hu ((hD _).mpr h))

end IntegrationInACVF.Section7
