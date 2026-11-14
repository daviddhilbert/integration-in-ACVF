import Integration7.GammaVolumeRVValidity
import Integration7.EssentialGammaVolumeSchemata
import IntegrationSection6.GammaIsomorphismSchemata

/-! Finite first-order volume-isomorphism witness data over the original
real/Gamma base. Validity checks an actual essential bijection, both volume
clauses and an explicitly bounded lower-dimensional exception schema.
Realization and promotion of complete witnesses are separate obligations. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaRVVolumeIsoSchema (B : Base (M := M)) (p a b k : ℕ)
    (sp : Fin p → SortTag := fun _ => .rv) where
  source : GammaRVVolumeSchema B p a k sp
  target : GammaRVVolumeSchema B p b k sp
  chart : Set (Fin ((p+a)+b) → M)
  chart_definable : DefinableOverBase B
    (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) chart
  supports : Finset (VolumeChartSupport (k+1))
  exceptionDegree : ℕ
  exceptionDegree_lt : exceptionDegree < k+1
  exception : GammaFiniteRVSchema B p ((k+1)+1) exceptionDegree sp

variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeIsoSchema.ordinary (F : GammaRVVolumeIsoSchema B p a b k sp) :
    GammaFiniteRVIsoSchema B p a b (k+1) sp where
  source := essentialFiniteVolumeSchema F.source.object
  target := essentialFiniteVolumeSchema F.target.object
  chart := F.chart
  chart_definable := F.chart_definable

def GammaRVVolumeIsoSchema.valid (F : GammaRVVolumeIsoSchema B p a b k sp) (z : Fin p → M) : Prop :=
  F.source.valid z ∧ F.target.valid z ∧ F.ordinary.valid z ∧ F.exception.valid z ∧
    volumeChartGammaRowValid F.source F.target F.chart z ∧
    volumeChartRVRowValid F.source F.target F.chart F.supports F.exception z

theorem GammaRVVolumeIsoSchema.valid_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaRVVolumeIsoSchema B p a b k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.source.valid_definable.inter (F.target.valid_definable.inter (F.ordinary.valid_definable.inter
    (F.exception.valid_definable.inter
      ((volumeChartGammaRowValid_definable hc F.source F.target F.chart_definable).inter
        (volumeChartRVRowValid_definable hc F.source F.target F.chart_definable F.supports F.exception)))))

end IntegrationInACVF.Section7
