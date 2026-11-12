import IntegrationSection6.GammaIsomorphismRealization
import IntegrationSection6.GammaNativeRawIsomorphisms
import IntegrationSection6.GammaTupleRelationPromotion

/-! Every actual finite Gamma RV isomorphism over a named sorted tuple
promotes to an isomorphism schema with a genuine definable validity locus
containing that tuple. All domain, volume and chart rows are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ}

theorem gamma_sorted_finite_isomorphism_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U V : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    ∃ F : GammaFiniteRVIsoSchema B p (rvObjectArity U.object) (rvObjectArity V.object) k sp,
      F.valid z ∧
      (∀ x, Fin.append z x ∈ F.source.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x s, Fin.append (Fin.append z x) s ∈ F.source.volume ↔ Fin.append x s ∈ gammaRawObjectVolume U.toGammaRVObject) ∧
      (∀ y, Fin.append z y ∈ F.target.domain ↔ y ∈ gammaRawObjectDomain V.toGammaRVObject) ∧
      (∀ y t, Fin.append (Fin.append z y) t ∈ F.target.volume ↔ Fin.append y t ∈ gammaRawObjectVolume V.toGammaRVObject) ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔ Fin.append x y ∈ gammaRawIsoGraph e) := by
  obtain ⟨A,hA,hAD,hAV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz U
  obtain ⟨C,hC,hCD,hCV⟩ := gamma_sorted_finite_object_promotion hκ hs hreal hgamma sp z hz V
  obtain ⟨H,hH,hHz⟩ := gamma_rv_tuple_relation_promotion B sp z hz
    (gammaRawIsoGraph e) (gammaRawIsoGraph_definable e)
  let F : GammaFiniteRVIsoSchema B p (rvObjectArity U.object) (rvObjectArity V.object) k sp := ⟨A,C,H,hH⟩
  refine ⟨F,⟨hA,hC,?_,?_⟩,hAD,hAV,hCD,hCV,hHz⟩
  · refine ⟨⟨hz,?_,?_,?_⟩,?_⟩
    · intro x hx
      obtain ⟨y,hy,hu⟩ := gammaRawIsoGraph_unique e x ((hAD x).mp hx)
      exact ⟨y,(hHz x y).mpr hy,fun y' hy' => hu y' ((hHz x y').mp hy')⟩
    · intro x y hxy
      obtain ⟨u,hx,_⟩ := (gammaRawIsoGraph_append_iff e x y).mp ((hHz x y).mp hxy)
      exact (hAD x).mpr ⟨u,hx⟩
    · intro y _
      have he : {x | Fin.append (Fin.append z x) y ∈ H} =
          {x | Fin.append x y ∈ gammaRawIsoGraph e} := Set.ext (fun x => hHz x y)
      change _ ∧ _
      rw [he]
      exact gammaRawIsoGraph_fibre_bound e y
    · intro y
      exact (hCD y).trans ((gammaRawIsoGraph_image e y).symm.trans
        (exists_congr (fun x => (hHz x y).symm)))
  · refine ⟨hz,?_⟩
    intro r _ hh hf hg
    exact gammaRawIsoGraph_weight e _ _ _ _
      ((hHz _ _).mp hh) ((hAV _ _).mp hf) ((hCV _ _).mp hg)

theorem gamma_finite_isomorphism_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval SortTag.vf (z i))
    (U V : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    ∃ F : GammaFiniteRVIsoSchema B p (rvObjectArity U.object) (rvObjectArity V.object) k,
      F.valid z ∧
      (∀ x, Fin.append z x ∈ F.source.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x s, Fin.append (Fin.append z x) s ∈ F.source.volume ↔ Fin.append x s ∈ gammaRawObjectVolume U.toGammaRVObject) ∧
      (∀ y, Fin.append z y ∈ F.target.domain ↔ y ∈ gammaRawObjectDomain V.toGammaRVObject) ∧
      (∀ y t, Fin.append (Fin.append z y) t ∈ F.target.volume ↔ Fin.append y t ∈ gammaRawObjectVolume V.toGammaRVObject) ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔ Fin.append x y ∈ gammaRawIsoGraph e) :=
  gamma_sorted_finite_isomorphism_promotion hκ hs hreal hgamma (fun _ => .vf) z hz U V e

end IntegrationInACVF.Section6
