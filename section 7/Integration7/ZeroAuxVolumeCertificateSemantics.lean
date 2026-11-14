import Integration7.VolumeEmptyParameterBlocks
import Integration7.GammaVolumeIsomorphismSchemata

/-! An empty auxiliary block gives exactly the ordinary supported
exception certificate. Adding or removing it preserves complete validity. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k j : ℕ} {sp : Fin p → SortTag}

theorem extraVolumeChartRVRowValid_empty
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    (H : Set (Fin ((p+a)+b) → M))
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (A : Finset (VolumeChartSupport (k+1))) (s0 : Fin 0 → SortTag)
    (E : GammaFiniteRVSchema B (p+0) ((k+1)+1) j (Fin.append sp s0))
    (E0 : GammaFiniteRVSchema B p ((k+1)+1) j sp) (hDom : E.domain = E0.domain) (z : Fin p → M) :
    extraVolumeChartRVRowValid F G H A E z ↔ volumeChartRVRowValid F G H A E0 z := by
  have hC := schemaVolumeCorrespondence_definable (weightedVolumeSchema F) (weightedVolumeSchema G) hH
  simp only [extraVolumeChartRVRowValid,extraWeightedPairsOutsideException,extraVolumeJacobianFormula,
    dropExtraVolumeParameters_zero,Function.comp_id,appendEmptySort_eq,hDom,Set.mem_ofPred_eq,
    volumeChartRVRowValid,weightedPairsOutsideException]
  constructor
  · rintro ⟨hz,hRV⟩
    exact ⟨hz,fun r hr => (hRV r ⟨hr,hC.proper _ hr.1⟩).1⟩
  · rintro ⟨hz,hRV⟩
    exact ⟨hz,fun r hr => ⟨hRV r hr.1,hr.2⟩⟩

def GammaRVVolumeIsoCertificateSchema.withoutAuxiliary
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0) :
    GammaRVVolumeIsoSchema B p a b k sp where
  source := H.source
  target := H.target
  chart := H.chart
  chart_definable := H.chart_definable
  supports := H.supports
  exceptionDegree := H.exceptionDegree
  exceptionDegree_lt := H.exceptionDegree_lt
  exception := H.zeroAuxiliaryException h

theorem GammaRVVolumeIsoCertificateSchema.withoutAuxiliary_valid
    (H : GammaRVVolumeIsoCertificateSchema B p a b k sp) (h : H.extraArity = 0)
    (z : Fin p → M) (hV : H.valid z) : (H.withoutAuxiliary h).valid z := by
  rcases H with ⟨F,G,H,hH,A,q,sq,j,hj,E⟩
  dsimp at h
  subst q
  rcases hV with ⟨hF,hG,hOrd,hΓ,y,hE,hRV⟩
  have he : Fin.append z y = z := funext (Fin.append_left z y)
  rw [he] at hE hRV
  let E0 := finiteSchemaChangeParameterSort (appendEmptySort_eq sp sq) E
  have hE0 : E0.valid z := by
    change finiteMapRowValid sp (fun _ => .rv) E.domain E.volume E.bound z
    change finiteMapRowValid (Fin.append sp sq) (fun _ => .rv) E.domain E.volume E.bound z at hE
    refine ⟨?_,hE.2⟩
    intro i
    exact (congrFun (appendEmptySort_eq sp sq) i) ▸ hE.1 i
  exact ⟨hF,hG,hOrd,hE0,hΓ,(extraVolumeChartRVRowValid_empty F G H hH A sq E E0 rfl z).mp hRV⟩

def GammaRVVolumeIsoSchema.toCertificate
    (H : GammaRVVolumeIsoSchema B p a b k sp) : GammaRVVolumeIsoCertificateSchema B p a b k sp where
  source := H.source
  target := H.target
  chart := H.chart
  chart_definable := H.chart_definable
  supports := H.supports
  extraArity := 0
  extraSort := Fin.elim0
  exceptionDegree := H.exceptionDegree
  exceptionDegree_lt := H.exceptionDegree_lt
  exception := finiteSchemaWithEmptyParameters H.exception

theorem GammaRVVolumeIsoSchema.toCertificate_valid
    (H : GammaRVVolumeIsoSchema B p a b k sp) (z : Fin p → M) (hV : H.valid z) :
    H.toCertificate.valid z := by
  rcases hV with ⟨hF,hG,hOrd,hE,hΓ,hRV⟩
  have he : Fin.append z (Fin.elim0 : Fin 0 → M) = z := funext (Fin.append_left z Fin.elim0)
  have hE' : (finiteSchemaWithEmptyParameters H.exception).valid z := by
    change finiteMapRowValid (Fin.append sp (Fin.elim0 : Fin 0 → SortTag)) (fun _ => .rv)
      H.exception.domain H.exception.volume H.exception.bound z
    refine ⟨?_,hE.2⟩
    intro i
    exact (congrFun (appendEmptySort_eq sp Fin.elim0) i).symm ▸ hE.1 i
  refine ⟨hF,hG,hOrd,hΓ,Fin.elim0,?_,?_⟩
  · change (finiteSchemaWithEmptyParameters H.exception).valid (Fin.append z Fin.elim0)
    rw [he]
    exact hE'
  · change extraVolumeChartRVRowValid H.source H.target H.chart H.supports
      (finiteSchemaWithEmptyParameters H.exception) (Fin.append z Fin.elim0)
    rw [he]
    exact (extraVolumeChartRVRowValid_empty H.source H.target H.chart H.chart_definable H.supports
      Fin.elim0 (finiteSchemaWithEmptyParameters H.exception) H.exception rfl z).mpr hRV

end IntegrationInACVF.Section7
