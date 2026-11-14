import Integration7.ExtraVolumeCertificateSemantics
import Integration7.GammaVolumeIsoSchemaRealization

/-! Realize an existential exception certificate after choosing its
auxiliary tuple internally. The essential bijection is reconstructed from
the original chart, independently of that tuple. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeIsoCertificateSchema.realizeInContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeIsoCertificateSchema B p a b k sp) (z : Fin p → M) (hz : F.valid z)
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.source.object.rowDomain z) (F.source.object.rowVolume z) (F.source.rowDensity z))
    (Q : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ b (k+1)
      (F.target.object.rowDomain z) (F.target.object.rowVolume z) (F.target.rowDensity z))
    (y : Fin F.extraArity → M) (hy : F.exception.valid (Fin.append z y))
    (hRV : extraVolumeChartRVRowValid F.source F.target F.chart F.supports F.exception (Fin.append z y))
    (E : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (Fin.append z y),B.gamma⟩ ((k+1)+1) F.exceptionDegree
      (F.exception.rowDomain (Fin.append z y)) (F.exception.rowVolume (Fin.append z y)))
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hE : E.codes ⊆ (C.base : Set M))
    (hH : (rawRVSpace (M := M) a).RelationDefinable (rawRVSpace (M := M) b) (C.base : Set M)
      (fun x y => Fin.append (Fin.append z (rvValues x)) (rvValues y) ∈ F.chart)) :
    ∃ e : RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject,
      ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔
        ∃ u : (P.inContext hc C hP).toObject.essential.obj.domain,
          rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y := by
  let U : PositiveRVVolumeObject (M := M) (C.base : Set M) k := (P.inContext hc C hP).toObject
  let V : PositiveRVVolumeObject (M := M) (C.base : Set M) k := (Q.inContext hc C hQ).toObject
  have hPU : RVVolumeSchemaRow U F.source z := P.inContext_schemaRow hc C F.source z hz.1 hP
  have hQV : RVVolumeSchemaRow V F.target z := Q.inContext_schemaRow hc C F.target z hz.2.1 hQ
  obtain ⟨e,he⟩ := exists_volumeSchemaUnderlyingIso hPU hQV F.chart F.chart_definable hz.2.2.1.2.2.1 hH
  let T := GammaFiniteGraphPresentation.inVolumeContext hc C E hE
  have hT (w) : w ∈ T.obj.domain.carrier ↔
      Fin.append (Fin.append z y) (rvValues w) ∈ F.exception.domain := by
    rw [GammaFiniteGraphPresentation.inVolumeContext_domain]
    rfl
  let f := rvVolumeIsoOfExtraSchemaRows hPU hQV e F.supports F.exception y he
    hz.2.2.2.1 hRV T.obj.domain hT T.obj.volume T.property F.exceptionDegree_lt
  exact ⟨f,he⟩

end IntegrationInACVF.Section7
