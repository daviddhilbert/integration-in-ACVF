import Integration7.IndexedVolumeChartRealization
import Integration7.IndexedVolumeRowEquality
import Integration7.VolumeChainSchemaRealization
import Integration7.RVVolumeInverse

/-! Indexed chart realization acts on arbitrary presentations of the
same full coordinate-and-density rows after a finite parameter extension. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeIsoCertificateSchema.indexedRealizeBetween
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (hSource : ∀ t ∈ T, H.source.sameRow F (rvValues t))
    (hTarget : ∀ t ∈ T, H.target.sameRow G (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      Nonempty (RVVolumeIso ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD)) := by
  let SP := H.source.indexedVolumePresentation BP (fun t ht => (hvalid t ht).1)
  let TP := H.target.indexedVolumePresentation BP (fun t ht => (hvalid t ht).2.1)
  obtain ⟨D₁,hCD₁,hSP⟩ := SP.exists_containingContext C hB
  obtain ⟨D₂,hD₁D₂,hTP⟩ := TP.exists_containingContext D₁ (hB.trans hCD₁)
  let hCD₂ := hCD₁.trans hD₁D₂
  let eP := H.source.indexedRowIso hc D₂ F BP hSource SP P
    (hSP.trans hD₁D₂) (hP.trans hCD₂)
  let eQ := H.target.indexedRowIso hc D₂ G BP hTarget TP Q hTP (hQ.trans hCD₂)
  obtain ⟨D₃,hD₂D₃,eH,_⟩ := H.indexedRealize hc D₂ BP hvalid SP TP
    (hSP.trans hD₁D₂) hTP (hBP.trans hCD₂) (hB.trans hCD₂)
  exact ⟨D₃,hCD₂.trans hD₂D₃,⟨((eP.extend hD₂D₃).symm hc D₃).trans hc D₃
    (eH.trans hc D₃ (eQ.extend hD₂D₃))⟩⟩

end IntegrationInACVF.Section7
