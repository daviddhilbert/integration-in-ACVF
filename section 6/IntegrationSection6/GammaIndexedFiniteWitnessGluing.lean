import IntegrationSection6.GammaIndexedBinaryPartitions
import IntegrationSection6.GammaIndexedEmpty
import IntegrationSection6.GammaCommonIndexedRealization

/-! A finite definable cover by common-blowup witnesses glues over any
actual RV[d] base. Regions can be infinite; all source, target and
intermediate objects remain in RV[d+k]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
open FiniteRV

theorem gamma_common_finite_indexed_glue {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (J : Finset (GammaFiniteCommonSchema F G)) :
    ∀ {T : Set (Fin p → RV (M := M))}
      {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
      (BP : GammaFiniteGraphPresentation B p d T R),
      (∀ t ∈ T, F.finiteRow (fun j => (t j).val)) → (∀ t ∈ T, G.finiteRow (fun j => (t j).val)) →
      (∀ t ∈ T, ∃ W ∈ J, W.valid (fun j => (t j).val)) →
      ∀ (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP),
      GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  induction J using Finset.induction_on with
  | empty =>
    intro T R BP hF hG hCover P Q
    apply gammaIndexed_empty_isp hκ hs h00 hreal F G BP ?_ P Q
    intro t ht
    obtain ⟨W,hW,_⟩ := hCover t ht
    exact Finset.notMem_empty W hW
  | @insert W J hNot ih =>
    intro T R BP hF hG hCover P Q
    let E : Set (Fin p → RV (M := M)) := {t | t ∈ T ∧ W.valid (fun j => (t j).val)}
    have hET : E ⊆ T := fun _ h => h.1
    have hWΓ : GammaSetDefinable B {t : Point (M := M) 0 p | W.valid (fun j => (t.2 j).val)} :=
      gamma_rv_set_from_tuple_formula W.valid_definable
    have hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E} :=
      (gammaLogicInput B).inter BP.domain_graph hWΓ
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    let PA := F.indexedPresentation_finiteRows BPA (fun t ht => hF t ht.1)
    let QA := G.indexedPresentation_finiteRows BPA (fun t ht => hG t ht.1)
    let PC := F.indexedPresentation_finiteRows BPC (fun t ht => hF t ht.1)
    let QC := G.indexedPresentation_finiteRows BPC (fun t ht => hG t ht.1)
    have hA := W.indexedRealizeAt hκ hs h00 hreal BPA (fun t ht => ht.2) PA QA
    have hCoverC : ∀ t ∈ T \ E, ∃ W ∈ J, W.valid (fun j => (t j).val) := by
      intro t ht
      obtain ⟨W',hW',hValid⟩ := hCover t ht.1
      rcases Finset.mem_insert.mp hW' with he | hj
      · subst W'
        exact False.elim (ht.2 ⟨ht.1,hValid⟩)
      · exact ⟨W',hj,hValid⟩
    have hC := ih BPC (fun t ht => hF t ht.1) (fun t ht => hG t ht.1) hCoverC PC QC
    exact gammaIndexed_binary_isp hκ hs h00 hreal F G BP E hET hEΓ P Q PA QA PC QC hA hC

end IntegrationInACVF.Section6
