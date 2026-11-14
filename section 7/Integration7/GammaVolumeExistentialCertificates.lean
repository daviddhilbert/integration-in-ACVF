import Integration7.ExtraVolumeRVValidity

/-! Auxiliary real parameters may witness only the small exceptional set
and its finite map. Existentially quantifying them keeps the validity locus
over the original base, while every geometric graph remains fixed. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaRVVolumeIsoCertificateSchema (B : Base (M := M)) (p a b k : ℕ)
    (sp : Fin p → SortTag := fun _ => .rv) where
  source : GammaRVVolumeSchema B p a k sp
  target : GammaRVVolumeSchema B p b k sp
  chart : Set (Fin ((p+a)+b) → M)
  chart_definable : DefinableOverBase B
    (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) chart
  supports : Finset (VolumeChartSupport (k+1))
  extraArity : ℕ
  extraSort : Fin extraArity → SortTag
  exceptionDegree : ℕ
  exceptionDegree_lt : exceptionDegree < k+1
  exception : GammaFiniteRVSchema B (p+extraArity) ((k+1)+1) exceptionDegree (Fin.append sp extraSort)

variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeIsoCertificateSchema.ordinary (F : GammaRVVolumeIsoCertificateSchema B p a b k sp) :
    GammaFiniteRVIsoSchema B p a b (k+1) sp where
  source := essentialFiniteVolumeSchema F.source.object
  target := essentialFiniteVolumeSchema F.target.object
  chart := F.chart
  chart_definable := F.chart_definable

def GammaRVVolumeIsoCertificateSchema.valid (F : GammaRVVolumeIsoCertificateSchema B p a b k sp)
    (z : Fin p → M) : Prop :=
  F.source.valid z ∧ F.target.valid z ∧ F.ordinary.valid z ∧
    volumeChartGammaRowValid F.source F.target F.chart z ∧
    ∃ y : Fin F.extraArity → M, F.exception.valid (Fin.append z y) ∧
      extraVolumeChartRVRowValid F.source F.target F.chart F.supports F.exception (Fin.append z y)

theorem GammaRVVolumeIsoCertificateSchema.valid_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (F : GammaRVVolumeIsoCertificateSchema B p a b k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.source.valid_definable.inter (F.target.valid_definable.inter (F.ordinary.valid_definable.inter
    ((volumeChartGammaRowValid_definable hc F.source F.target F.chart_definable).inter
      (gamma_family_row_exists_definable sp F.extraSort (F.exception.valid_definable.inter
        (extraVolumeChartRVRowValid_definable hc F.source F.target F.chart_definable F.supports F.exception))))))

end IntegrationInACVF.Section7
