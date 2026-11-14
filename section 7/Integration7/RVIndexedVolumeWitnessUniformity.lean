import Integration7.IndexedVolumeFiniteWitnessGluing
import IntegrationSection6.GammaNativeRawObjects
import IntegrationSection6.GammaWitnessUniformity

/-! Pointwise original-Gamma formula witnesses yield common forward
volume blowups of the whole indexed objects. A finite witness cover is
constructed by compactness and then glued geometrically. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}

theorem gamma_rv_indexed_volume_witness_uniformity {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hWitness : ∀ t ∈ T, ∃ H : GammaVolumeCommonSchema F G, H.valid (rvValues t))
    (C : BaseContext M) (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      VolumeBlowupEquivalent ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD) := by
  let A := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  have hA : DefinableOverBase B (fun _ : Fin p => .rv) A :=
    gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject
  obtain ⟨J, hJ⟩ := gamma_finite_witnesses hκ hs hreal hgamma (fun _ => .rv) A hA
    (fun H : GammaVolumeCommonSchema F G => {z | H.valid z})
    (fun H => H.valid_definable hc) (by
      rintro z ⟨u,rfl⟩
      exact hWitness u.val ((Set.ext_iff.mp BP.domain_eq u.val).mp u.property))
  apply gamma_volume_common_finite_indexed_glue hc F G J C BP hF hG ?_ P Q hP hQ hBP hB
  intro t ht
  apply hJ _
  exact ⟨⟨t,(Set.ext_iff.mp BP.domain_eq t).mpr ht⟩,rfl⟩

end IntegrationInACVF.Section7
