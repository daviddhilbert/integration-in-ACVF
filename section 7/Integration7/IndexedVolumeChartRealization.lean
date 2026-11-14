import Integration7.IndexedVolumeIsomorphisms

/-! The joint original-Gamma chart becomes definable in a finite
containing context, yielding an actual indexed volume isomorphism. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeIsoCertificateSchema.indexedRealize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      ∃ f : RVVolumeIso ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD),
        ∀ u v, indexedVolumeChartRelation H u.val v.val ↔ finiteIsoMap f.iso u = v := by
  obtain ⟨e,t,hR⟩ := gamma_rv_relation_real_specialize (indexedVolumeChartRelation_gammaGraph H)
  let D := finiteVolumeParameterContext C (Set.range (rawTuple t)) (Set.finite_range _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    Set.subset_union_left.trans (finiteVolumeParameterContext_contains C _ _)
  have hCodes : B.real ∪ Set.range (rawTuple t) ⊆ (D.base : Set M) := by
    intro x hx
    rcases hx with hx | hx
    · exact hCD (hB hx)
    · exact finiteVolumeParameterContext_contains C _ _ (Or.inr hx)
  have hDef := (canonicalRawRVRelation hc _ hR).mono _ _ hCodes
  obtain ⟨e,he⟩ := exists_indexedVolumeUnderlyingIso hc D H BP hvalid P Q
    (hP.trans hCD) (hQ.trans hCD) hDef
  exact ⟨D,hCD,indexedVolumeIso hc D H BP hvalid P Q (hP.trans hCD) (hQ.trans hCD)
    (hBP.trans hCD) (hB.trans hCD) e he,he⟩

end IntegrationInACVF.Section7
