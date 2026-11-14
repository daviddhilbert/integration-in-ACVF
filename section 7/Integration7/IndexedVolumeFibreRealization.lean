import Integration7.IndexedVolumeFibreComparisons
import Integration7.VolumeCertificateSmallContextRealization

/-! Each original indexed chart has an actual fibre volume isomorphism
in a containing context small at the original saturation cardinal.
No uniform choice of its additional parameters is asserted. -/

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

theorem exists_indexedRowVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hB : B.real ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : t ∈ T) (hz : H.valid (rvValues t)) :
    ∃ (D : BaseContext M) (hS : (C.base : Set M) ∪ Set.range (rvValues t) ⊆ (D.base : Set M)),
      Cardinal.mk (D.base : Set M) < C.κ ∧
      ∃ f : RVVolumeIso ((indexedRowVolumeObject hc C P hP t).extend hS)
        ((indexedRowVolumeObject hc C Q hQ t).extend hS),
        ∀ x y, Fin.append (Fin.append (rvValues t) x) y ∈ H.chart ↔
          ∃ u : ((indexedRowVolumeObject hc C P hP t).extend hS).essential.obj.domain,
            rvValues u.val = x ∧ rvValues (finiteIsoMap f.iso u).val = y := by
  let Cₜ := finiteVolumeParameterContext C (Set.range (rvValues t)) (Set.finite_range _)
  have h0 : (C.base : Set M) ∪ Set.range (rvValues t) ⊆ (Cₜ.base : Set M) :=
    finiteVolumeParameterContext_contains C _ _
  have PU := (indexedRow_schemaRow hc C P hP t ht hz.1).extend h0
  have PV := (indexedRow_schemaRow hc C Q hQ t ht hz.2.1).extend h0
  obtain ⟨D,hD,hsmall,f,hf⟩ := GammaRVVolumeIsoCertificateSchema.realizeOnWithSmallBase
    (U := (indexedRowVolumeObject hc C P hP t).extend h0)
    (V := (indexedRowVolumeObject hc C Q hQ t).extend h0)
    hc Cₜ H (rvValues t) hz PU PV
    (hB.trans (Set.subset_union_left.trans h0)) (Set.subset_union_right.trans h0)
  exact ⟨D,h0.trans hD,hsmall,f,hf⟩

end IntegrationInACVF.Section7
