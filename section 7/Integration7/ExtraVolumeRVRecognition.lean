import Integration7.WeightedSchemaRowFibres
import Integration7.ExtraVolumeCertificateSemantics

/-! Actual finite chart certificates imply the first-order RV clause.
The exception row is interpreted exactly on weighted labels; auxiliary
parameters enter neither the geometric correspondence nor its chart. -/

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

theorem RVVolumeSchemaRow.extraRVRowValid_of_charts (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (hF : F.valid z) (hG : G.valid z)
    (e : U.essential ≅ V.essential) (A : Finset (VolumeChartSupport (k+1)))
    (E : GammaFiniteRVSchema B (p+q) ((k+1)+1) j (Fin.append sp sq)) (y : Fin q → M)
    (hE : E.valid (Fin.append z y))
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (D : Set (Fin ((k+1)+1) → CanonicalRV.RVSort M))
    (hD : ∀ w, w ∈ D ↔ Fin.append (Fin.append z y) (rvValues w) ∈ E.domain)
    (hA : ∀ u, volumeGammaWeightTuple U u ∉ D → volumeIsoChartAt e A u) :
    extraVolumeChartRVRowValid F G H A E (Fin.append z y) := by
  refine ⟨hE.1,?_⟩
  intro r hr
  have hC := hr.1.1
  rw [append_dropExtraVolumeParameters] at hC
  obtain ⟨u,hu⟩ := (P.weighted_correspondence_iff Q hF hG e H hH r).mp hC
  have he : Fin.append (Fin.append z y)
        (Fin.append (rvValues (volumeGammaWeightTuple U u))
          (rvValues (volumeGammaWeightTuple V (finiteIsoMap e u)))) ∘
      weightedPairSourceIndices (p+q) (k+1) =
        Fin.append (Fin.append z y) (rvValues (volumeGammaWeightTuple U u)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [Function.comp_apply,weightedPairSourceIndices,Fin.addCases_left,
        Fin.addCases_right,Fin.append_left,Fin.append_right]
  have hn : volumeGammaWeightTuple U u ∉ D := by
    intro hmem
    have hnot := hr.1.2
    rw [← hu,he] at hnot
    exact hnot ((hD _).mp hmem)
  have hJ := hA u hn
  change (∃ σ ∈ A, VolumeChartValue σ (volumeCorrespondence (finiteIsoMap e)).carrier
    (productTuple (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u)))
    (fun _ => U.essentialForm.value u / V.essentialForm.value (finiteIsoMap e u))) at hJ
  rw [← P.correspondence_eq Q e H hF.1.1 hH] at hJ
  refine ⟨?_,hr.2⟩
  rw [append_dropExtraVolumeParameters,← hu,volumeGammaWeightTuple_raw_append,volumeGammaWeightTuple_raw_append]
  change weightedPairTuple z (rvValues (U.essential.obj.value u))
      (rvValues (V.essential.obj.value (finiteIsoMap e u)))
      (fun _ : Fin 1 => (U.essentialForm.value u).val)
      (fun _ : Fin 1 => (V.essentialForm.value (finiteIsoMap e u)).val) ∈ supportedSchemaJacobianFormula F G H A
  exact (supportedSchemaJacobianFormula_typed_iff F G H A z _ _ _ _ hF.1.1
    (U.essentialForm_nonzero u) (V.essentialForm_nonzero (finiteIsoMap e u))).mpr hJ

end IntegrationInACVF.Section7
