import Integration7.VolumeSchemaOrdinaryValidity
import Integration7.ExtraVolumeRVRecognition

/-! Recognize a complete finite certificate from actual volume geometry.
Ordinary chart validity and both volume clauses are proved from the
isomorphism and its finite chart certificate, not assumed separately. -/

noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoCertificateSchema.valid_of_rows
    {U V : PositiveRVVolumeObject (M := M) S k}
    (F : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp)
    (z : Fin p → M) (hF : F.source.valid z) (hG : F.target.valid z)
    (P : RVVolumeSchemaRow U F.source z) (Q : RVVolumeSchemaRow V F.target z)
    (e : RVVolumeIso U V)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y)
    (y : Fin F.extraArity → M) (hE : F.exception.valid (Fin.append z y))
    (D : Set (Fin ((k+1)+1) → CanonicalRV.RVSort M))
    (hD : ∀ w, w ∈ D ↔ Fin.append (Fin.append z y) (rvValues w) ∈ F.exception.domain)
    (hA : ∀ u, volumeGammaWeightTuple U u ∉ D → volumeIsoChartAt e.iso F.supports u) :
    F.valid z := by
  refine ⟨hF,hG,?_,P.gammaRowValid_of_iso Q hF hG e F.chart hH,
    y,hE,P.extraRVRowValid_of_charts Q hF hG e.iso F.supports F.exception y hE hH D hD hA⟩
  exact ⟨essentialFiniteVolumeSchema_valid F.source.object z hF.1,
    essentialFiniteVolumeSchema_valid F.target.object z hG.1,
    P.bijectiveRowValid Q hF.1.1 e.iso hH,
    essentialVolumeChart_weight_valid F.source.object F.target.object F.chart z hF.1.1⟩

end IntegrationInACVF.Section7
