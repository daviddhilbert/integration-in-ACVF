import Integration7.IndexedVolumeBadFibreDimension
import Integration7.IndexedVolumeGammaCompatibility
import Integration7.RVMapDisagreement
import Integration7.RVParameterFibreDimension
import Integration7.FiniteVolumeCertificateCriterion

/-! Uniform valid original-Gamma volume charts yield the actual joint
volume isomorphism. Local exceptional parameters are handled by dimension
descent, rather than by a definable choice of fibre witnesses. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def indexedVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M))
    (e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential)
    (hChart : ∀ u v, indexedVolumeChartRelation H u.val v.val ↔ finiteIsoMap e u = v) :
    RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject where
  iso := e
  gamma u := gammaVolumeEquation_of_weight e u
    (indexedVolume_gammaWeight hc C H BP hvalid P Q hP hQ e
      (fun u => (hChart u (finiteIsoMap e u)).mpr rfl) u)
  rv := by
    let U := (P.inContext hc C hP).toObject
    let V := (Q.inContext hc C hQ).toObject
    obtain ⟨ω,D,hDU,hD,hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ (d+k))
      e U.essential_nonzero V.essential_nonzero
    let A := (volumeJacobianDisagreement e ω).sdiff D
    have hAU : A.carrier ⊆ U.essential.obj.domain.carrier := by
      rintro x ⟨⟨u,rfl,_⟩,_⟩
      exact u.property
    have hBad (u : A) :
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (U.essential.obj.value ⟨u.val,hAU u.property⟩)
          (V.essential.obj.value (finiteIsoMap e ⟨u.val,hAU u.property⟩))
          ((ω ⟨u.val,hAU u.property⟩).val 0) ∧
        (ω ⟨u.val,hAU u.property⟩).val 0 ≠ volumeRatio U V e ⟨u.val,hAU u.property⟩ :=
      ⟨hω ⟨u.val,hAU u.property⟩ u.property.2,
        (volumeJacobianDisagreement_mem e ω ⟨u.val,hAU u.property⟩).mp u.property.1⟩
    let K := (canonicalRawRVDomain hc BP.domain).extend hBP
    let f := (canonicalRawRVMap hc BP.volume).extend hBP
    have hFinite : f.FiniteFibres := BP.finite_volume
    have hK : rvDim K ≤ d :=
      (rvDim_le_of_finite_map f hFinite).trans (rvDim_le_arity _)
    have hAK (u : A) : u.val ∘ Fin.castAdd a ∈ K.carrier := by
      have h := (indexedVolume_essential_domain_iff hc C P hP (fun t ht => (hvalid t ht).1)
        u.val).mp (hAU u.property)
      exact (Set.ext_iff.mp BP.domain_eq (u.val ∘ Fin.castAdd a)).mpr h.1
    have hA : rvDim A < (d+k)+1 := by
      apply rvDim_lt_base_add_tuple_fibre hc C A K hAK hK
      intro t
      have ht : t.val ∈ T := (Set.ext_iff.mp BP.domain_eq t.val).mp t.property
      exact indexedVolume_bad_fibre_dim hc C H BP hvalid P Q hP hQ e hChart hB ω A hAU hBad t.val ht
    let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
    refine ⟨D.union A,Set.union_subset hDU hAU,
      (rvDim_union_le_max hc hex C.saturated C.small D A).trans_lt (max_lt hD hA),?_⟩
    intro u hu
    have huD : u.val ∉ D.carrier := fun h => hu (Or.inl h)
    have he : (ω u).val 0 = volumeRatio U V e u := by
      by_contra hn
      exact hu (Or.inr ⟨(volumeJacobianDisagreement_mem e ω u).mpr hn,huD⟩)
    rw [← he]
    exact hω u huD

end IntegrationInACVF.Section7
