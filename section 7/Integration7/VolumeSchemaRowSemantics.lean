import Integration7.TupleVolumeChartSemantics
import Integration7.GammaVolumePresentationContexts
import Integration7.VolumeGammaWeightTuples

/-! Exact interpretation of coordinate and density schemata on actual
finite volume objects. These graph equalities supply semantic bridges;
they do not assume any volume-preserving comparison. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

structure RVVolumeSchemaRow (U : PositiveRVVolumeObject (M := M) S k)
    (F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp) (z : Fin p → M) : Prop where
  volume_iff : ∀ x t, F.object.rowVolume z x t ↔
    ∃ u : U.underlying.obj.domain, u.val = x ∧ U.underlying.obj.value u = t
  density_iff : ∀ x ω, F.rowDensity z x ω ↔
    ∃ u : U.underlying.obj.domain, u.val = x ∧ (U.form.map u).val = ω

variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}

theorem RVVolumeSchemaRow.volume_at (P : RVVolumeSchemaRow U F z)
    (u : U.essential.obj.domain) : F.object.rowVolume z u.val (U.essential.obj.value u) :=
  (P.volume_iff _ _).mpr ⟨⟨u.val,rvEssentialLabels_subset _ u.property⟩,rfl,rfl⟩

theorem RVVolumeSchemaRow.density_at (P : RVVolumeSchemaRow U F z)
    (u : U.essential.obj.domain) : F.rowDensity z u.val (fun _ => U.essentialForm.value u) := by
  apply (P.density_iff _ _).mpr
  refine ⟨⟨u.val,rvEssentialLabels_subset _ u.property⟩,rfl,?_⟩
  funext i
  fin_cases i
  rfl

theorem volumeGammaWeightTuple_raw_append
    (u : U.essential.obj.domain) :
    rvValues (volumeGammaWeightTuple U u) =
      Fin.append (rvValues (U.essential.obj.value u)) (fun _ : Fin 1 => (U.essentialForm.value u).val) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      change (volumeGammaWeightTuple U u i.castSucc).val = _
      simp only [volumeGammaWeightTuple,Fin.snoc_castSucc]
      rfl
    · fin_cases i
      simp only [Fin.append_right]
      change (volumeGammaWeightTuple U u (Fin.last (k+1))).val = _
      simp only [volumeGammaWeightTuple,Fin.snoc_last]
theorem RVVolumeSchemaRow.weighted_at (P : RVVolumeSchemaRow U F z)
    (u : U.essential.obj.domain) :
    Fin.append (Fin.append z (rvValues u.val)) (rvValues (volumeGammaWeightTuple U u)) ∈ weightedVolumeGraph F := by
  rw [volumeGammaWeightTuple_raw_append,weightedVolumeGraph_append]
  exact ⟨P.volume_at u,P.density_at u⟩

theorem RVVolumeSchemaRow.correspondence_eq (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (e : U.essential ≅ V.essential)
    (H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M))
    (hz : ∀ i, sortEval (sp i) (z i))
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y) :
    {r | Fin.append z (rvValues r) ∈ schemaVolumeCorrespondence F.object G.object H} =
      (volumeCorrespondence (finiteIsoMap e)).carrier := by
  ext r
  let t := r ∘ productLeft (k+1) (k+1)
  let s := r ∘ productRight (k+1) (k+1)
  have hr : productTuple t s = r := by
    apply productTuple_ext <;> intro i
    · exact productTuple_left _ _ i
    · exact productTuple_right _ _ i
  change (Fin.append z (rvValues r) ∈ schemaVolumeCorrespondence F.object G.object H) ↔ _
  rw [← hr,rvValues_productTuple_eq_append,
    schemaVolumeCorrespondence_append F.object G.object H z (rvValues t) (rvValues s)
      hz (fun i => (t i).property) (fun i => (s i).property)]
  constructor
  · rintro ⟨x,y,hx,hxy,hy⟩
    obtain ⟨u,rfl,rfl⟩ := (hH x y).mp hxy
    obtain ⟨u',hu',hut⟩ := (P.volume_iff u.val t).mp hx
    obtain ⟨v',hv',hvs⟩ := (Q.volume_iff (finiteIsoMap e u).val s).mp hy
    have hu : u' = ⟨u.val,rvEssentialLabels_subset _ u.property⟩ := Subtype.ext hu'
    have hv : v' = ⟨(finiteIsoMap e u).val,rvEssentialLabels_subset _ (finiteIsoMap e u).property⟩ := Subtype.ext hv'
    subst u'
    subst v'
    exact ⟨u,congrArg₂ productTuple hut hvs⟩
  · rintro ⟨u,hu⟩
    have ht : U.essential.obj.value u = t := by
      funext i
      have h := congrFun hu (productLeft (k+1) (k+1) i)
      simpa only [productTuple_left] using h
    have hs : V.essential.obj.value (finiteIsoMap e u) = s := by
      funext i
      have h := congrFun hu (productRight (k+1) (k+1) i)
      simpa only [productTuple_right] using h
    refine ⟨rvValues u.val,rvValues (finiteIsoMap e u).val,?_,(hH _ _).mpr ⟨u,rfl,rfl⟩,?_⟩
    · exact ht ▸ P.volume_at u
    · exact hs ▸ Q.volume_at (finiteIsoMap e u)

end IntegrationInACVF.Section7
