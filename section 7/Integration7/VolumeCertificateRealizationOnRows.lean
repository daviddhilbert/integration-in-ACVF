import Integration7.GammaVolumeCertificateRealization

/-! A valid volume-comparison certificate acts on any actual objects
interpreting its rows. The exact original chart is reconstructed on those
objects, rather than on newly chosen endpoint presentations. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoCertificateSchema.realizeOnRows
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (F : GammaRVVolumeIsoCertificateSchema B p U.underlying.obj.arity V.underlying.obj.arity k sp)
    (z : Fin p → M) (hz : F.valid z)
    (P : RVVolumeSchemaRow U F.source z) (Q : RVVolumeSchemaRow V F.target z)
    (y : Fin F.extraArity → M)
    (hRV : extraVolumeChartRVRowValid F.source F.target F.chart F.supports F.exception (Fin.append z y))
    (E : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (Fin.append z y),B.gamma⟩ ((k+1)+1) F.exceptionDegree
      (F.exception.rowDomain (Fin.append z y)) (F.exception.rowVolume (Fin.append z y)))
    (hE : E.codes ⊆ (C.base : Set M))
    (hH : (rawRVSpace (M := M) U.underlying.obj.arity).RelationDefinable
      (rawRVSpace (M := M) V.underlying.obj.arity) (C.base : Set M)
      (fun x y => Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ F.chart)) :
    ∃ e : RVVolumeIso U V, ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  obtain ⟨e,he⟩ := exists_volumeSchemaUnderlyingIso P Q F.chart F.chart_definable hz.2.2.1.2.2.1 hH
  let T := GammaFiniteGraphPresentation.inVolumeContext hc C E hE
  have hT (w) : w ∈ T.obj.domain.carrier ↔
      Fin.append (Fin.append z y) (rvValues w) ∈ F.exception.domain := by
    rw [GammaFiniteGraphPresentation.inVolumeContext_domain]
    rfl
  let f := rvVolumeIsoOfExtraSchemaRows P Q e F.supports F.exception y he hz.2.2.2.1 hRV
    T.obj.domain hT T.obj.volume T.property F.exceptionDegree_lt
  exact ⟨f,he⟩

end IntegrationInACVF.Section7
