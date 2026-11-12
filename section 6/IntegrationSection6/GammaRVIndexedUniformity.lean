import IntegrationSection6.GammaCommonFiniteRowCompactness
import IntegrationSection6.GammaIndexedFiniteWitnessGluing

/-! Pointwise original-Gamma common blowups glue over a finite-volume RV
index base. Genuine witness compactness and finite geometric partitioning
replace any assumption that the abstract Isp predicate is definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Milestone0.sortEval
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
open FiniteRV

theorem gamma_rv_indexed_common_uniformity_at {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val))
    (hG : ∀ t ∈ T, G.finiteRow (fun j => (t j).val))
    (hCommon : ∀ t ∈ T,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ a k
        (F.rowDomain (fun j => (t j).val)) (F.rowVolume (fun j => (t j).val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ b k
        (G.rowDomain (fun j => (t j).val)) (G.rowVolume (fun j => (t j).val)),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (t j).val)) P.toGamma Q.toGamma)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) :
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  let A := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  have hA : DefinableOverBase B (fun _ : Fin p => .rv) A := gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject
  have hFA : ∀ z ∈ A, F.finiteRow z := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    exact hF u.val ((Set.ext_iff.mp BP.domain_eq u.val).mp u.property)
  have hGA : ∀ z ∈ A, G.finiteRow z := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    exact hG u.val ((Set.ext_iff.mp BP.domain_eq u.val).mp u.property)
  have hCommonA : ∀ z ∈ A,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k (F.rowDomain z) (F.rowVolume z),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b k (G.rowDomain z) (G.rowVolume z),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal z) P.toGamma Q.toGamma := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    exact hCommon u.val ((Set.ext_iff.mp BP.domain_eq u.val).mp u.property)
  obtain ⟨J,hJ⟩ := gamma_common_finite_cover_of_finiteRows hκ hs h00 hreal hgamma F G A hA hFA hGA hCommonA
  have hCover : ∀ t ∈ T, ∃ W ∈ J, W.valid (fun j => (t j).val) := by
    intro t ht
    apply hJ _
    exact ⟨⟨t,(Set.ext_iff.mp BP.domain_eq t).mpr ht⟩,rfl⟩
  exact gamma_common_finite_indexed_glue hκ hs h00 hreal F G J BP hF hG hCover P Q

theorem gamma_rv_indexed_common_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.finiteRow (fun j => (t j).val))
    (hG : ∀ t ∈ T, G.finiteRow (fun j => (t j).val))
    (hCommon : ∀ t ∈ T,
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ a k
        (F.rowDomain (fun j => (t j).val)) (F.rowVolume (fun j => (t j).val)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ b k
        (G.rowDomain (fun j => (t j).val)) (G.rowVolume (fun j => (t j).val)),
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (t j).val)) P.toGamma Q.toGamma)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP) : GammaIsp hκ hs h00 hreal P.toGamma Q.toGamma :=
  ⟨Set.univ,Set.subset_univ _,Set.subset_univ _,
    gamma_rv_indexed_common_uniformity_at hκ hs h00 hreal hgamma F G BP hF hG hCommon P Q⟩

end IntegrationInACVF.Section6
